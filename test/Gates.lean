import EventB.Model
import EventB.Formula.Parse
import EventB.Prover.Local
import EventB.Typing.Check
import EventB.POG

namespace EventB.Gates

open EventB
open EventB.Formula
open EventB.Prover.Local
open EventB.Typing
open EventB.POG

structure FileResult where
  path : String
  status : String
  model : Option Model := none

def expectedInventory : List (String × Nat) :=
  [("guard", 467), ("action", 410), ("event", 308), ("refinesEvent", 222),
   ("variable", 180), ("invariant", 142), ("parameter", 137), ("axiom", 68),
   ("constant", 33), ("machineFile", 22), ("seesContext", 22),
   ("refinesMachine", 19), ("extendsContext", 17), ("contextFile", 16),
   ("witness", 15), ("carrierSet", 6)]

private def isSource (path : System.FilePath) : Bool :=
  path.toString.endsWith ".bum" || path.toString.endsWith ".buc"

private def sourceFiles : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  let corpus : System.FilePath := "corpus"
  for project in ← corpus.readDir do
    -- corpus/ holds MANIFEST.tsv alongside the project directories.
    if ← project.path.isDir then
      for entry in ← project.path.readDir do
        if isSource entry.path then
          paths := entry.path :: paths
  pure (paths.mergeSort (fun left right => left.toString < right.toString))

private def shortReason (reason : String) : String :=
  reason.splitOn "\n" |>.head?.getD "parse failed"

private def checkFile (path : System.FilePath) : IO FileResult := do
  try
    let source ← IO.FS.readBinFile path
    let parsed :=
      if path.toString.endsWith ".bum" then
        parseMachine source
      else
        parseContext source
    match parsed with
    | .ok model => pure { path := path.toString, status := "PASS", model := some model }
    | .error reason =>
        pure { path := path.toString,
               status := "FAIL:" ++ shortReason (EventB.Error.render reason) }
  catch err =>
    pure { path := path.toString, status := "FAIL:IO " ++ err.toString }

private def sumInventory : List (String × Nat) → List (String × Nat) →
    List (String × Nat)
  | [], _ => []
  | _, [] => []
  | (name, left) :: xs, (_, right) :: ys =>
      (name, left + right) :: sumInventory xs ys

private def totalInventory (results : List FileResult) : List (String × Nat) :=
  results.foldl
    (fun total result =>
      match result.model with
      | some model => sumInventory total model.inventory
      | none => total)
    (expectedInventory.map (fun (name, _) => (name, 0)))

private def histogramAdd (reason : String) : List (String × Nat) → List (String × Nat)
  | [] => [(reason, 1)]
  | (name, count) :: rest =>
      if name == reason then
        (name, count + 1) :: rest
      else
        (name, count) :: histogramAdd reason rest

private def histogram (results : List FileResult) : List (String × Nat) :=
  (results.foldl
    (fun counts result =>
      if result.status.startsWith "FAIL:" then
        histogramAdd result.status counts
      else
        counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)


/-- P1 gate. Every formula must parse, and reparsing the printed form must give back the
same tree: a printer that lost an operator, or a precedence bug that quietly rebracketed,
would pass a parse-only check. Denominator 1102, from `scripts/manifest.py`. -/
private def formulaCount : Nat := 1102

private structure FormulaResult where
  key    : String
  status : String

private def checkFormula (file label formula : String) : FormulaResult :=
  let key := file ++ "\t" ++ label
  match Formula.parse formula with
  | .error reason => { key := key, status := "FAIL:" ++ EventB.Error.render reason }
  | .ok term =>
      match Formula.parse (Formula.print term) with
      | .error reason =>
          { key := key, status := "FAIL:reprint " ++ EventB.Error.render reason }
      | .ok again =>
          if again == term then { key := key, status := "PASS" }
          else { key := key, status := "FAIL:round-trip differs" }

private def formulaResults (results : List FileResult) : List FormulaResult :=
  results.flatMap fun result =>
    match result.model with
    | none => []
    | some model => model.formulas.map (fun (label, f) => checkFormula result.path label f)

private def formulaHistogram (results : List FormulaResult) : List (String × Nat) :=
  (results.foldl
    (fun counts result =>
      if result.status.startsWith "FAIL:" then histogramAdd result.status counts
      else counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)


/-- P2 gate. Rodin recorded, in every `.bpo`, the type it inferred for each identifier
in scope. Nothing in the `.bum` states those types, so matching them means reproducing
the static checker. 940 distinct (file, identifier) pairs, 2019 assertions with the
repeats Rodin writes across predicate sets. -/
private def typeCount : Nat := 940

mutual

/-- Pull `<org.eventb.core.poIdentifier name=... type=.../>` out of a `.bpo`. The root is
`poFile`, outside the machine/context element set, so this walks the raw XML tree rather
than the Event-B model. The first spelling of each name wins; the corpus never types one
name two ways within a file. -/
private def rawIdentifiers (e : XmlElem) : List (String × String) :=
  let here :=
    if e.tag == "org.eventb.core.poIdentifier" then
      -- Rodin writes the identifier name as a plain `name` attribute, unnamespaced.
      match e.attr? "name", e.attr? "org.eventb.core.type" with
      | some n, some t => [(n, t)]
      | _, _ => []
    else []
  here ++ rawIdentifiersList e.children
termination_by sizeOf e
decreasing_by cases e; simp +arith

private def rawIdentifiersList : List XmlElem → List (String × String)
  | [] => []
  | e :: es => rawIdentifiers e ++ rawIdentifiersList es
termination_by es => sizeOf es

end

private def dedupFirst : List (String × String) → List (String × String) →
    List (String × String)
  | [], acc => acc.reverse
  | (n, t) :: rest, acc =>
      if acc.any (fun p => p.1 == n) then dedupFirst rest acc
      else dedupFirst rest ((n, t) :: acc)

private def readGoldTypes (path : System.FilePath) : IO (List (String × String)) := do
  match parseXml (← IO.FS.readBinFile path) with
  | .error _ => return []
  | .ok xml => return dedupFirst (rawIdentifiers xml) []

private structure TypeResult where
  key    : String
  status : String

/-- Compare inferred against recorded by parsing both, so a mismatch is reported as two
types rather than a diff of Unicode. -/
private def compareType (key inferred gold : String) : TypeResult :=
  if inferred == gold then { key := key, status := "PASS" }
  else match Ty.parse gold with
    | none => { key := key, status := s!"FAIL:ungrammatical gold type {gold}" }
    | some _ => { key := key, status := s!"FAIL:inferred {inferred}, recorded {gold}" }

private def checkTypes (project : Project) (file : String)
    (gold : List (String × String)) : List TypeResult :=
  match inferComponent project file with
  | .error e =>
      gold.map (fun (n, _) =>
        { key := file ++ "\t" ++ n, status := "FAIL:" ++ EventB.Error.render e })
  | .ok (env, _) =>
      gold.map fun (n, g) =>
        let key := file ++ "\t" ++ n
        match env.find? (fun p => p.1 == n) with
        | none => { key := key, status := "FAIL:not inferred" }
        | some (_, t) => compareType key t.print g

private def typeHistogram (results : List TypeResult) : List (String × Nat) :=
  (results.foldl
    (fun counts r => if r.status.startsWith "FAIL:" then histogramAdd r.status counts
                     else counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)


/-- P3 gate. Rodin recorded every obligation it generated, so the gate is a set
comparison in both directions: a missing obligation is unsoundness, and a spurious one
is work nobody has to do. 1133 sequents in the corpus. -/
private def sequentCount : Nat := 1133

/-- Rodin's own discharge record, from the `.bps` files: it closed all 1133, 1088 without
a human. That is the P4 bar, and the number any prover backend is measured against. -/
private def rodinAuto : Nat := 1088
private def rodinManual : Nat := 45

mutual

private def poNames (e : XmlElem) : List String :=
  let here :=
    if e.tag == "org.eventb.core.poSequent" then (e.attr? "name").toList else []
  here ++ poNamesList e.children
termination_by sizeOf e
decreasing_by cases e; simp +arith

private def poNamesList : List XmlElem → List String
  | [] => []
  | e :: es => poNames e ++ poNamesList es
termination_by es => sizeOf es

end

private def readGoldPOs (path : System.FilePath) : IO (List String) := do
  match parseXml (← IO.FS.readBinFile path) with
  | .error _ => return []
  | .ok xml => return poNames xml

private structure PoResult where
  key    : String
  status : String

/-- Both directions, one line per obligation, so `--histogram` separates "we missed it"
from "we invented it". -/
private def checkPOs (project : Project) (file : String) (gold : List String) :
    List PoResult :=
  let ours := (generate project file).map (·.name)
  let missing := gold.filter (fun n => !ours.contains n)
    |>.map fun n => { key := file ++ "\t" ++ n, status := "FAIL:not generated" }
  let spurious := ours.filter (fun n => !gold.contains n)
    |>.map fun n => { key := file ++ "\t" ++ n, status := "FAIL:not in .bpo" }
  let matched := gold.filter (fun n => ours.contains n)
    |>.map fun n => { key := file ++ "\t" ++ n, status := "PASS" }
  matched ++ missing ++ spurious

private def poHistogram (results : List PoResult) : List (String × Nat) :=
  (results.foldl
    (fun counts r =>
      if r.status.startsWith "FAIL:" then
        -- Group by class as well as direction: INV and GRD fail for different reasons.
        histogramAdd (r.status ++ " " ++ ((r.key.splitOn "/").getLast!)) counts
      else counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)


/-- P3b gate. A PO name can match while the statement is nonsense, so once the generator
derives goals they are compared against the `org.eventb.core.predicate` Rodin recorded on
the same sequent. Modulo type ascriptions, which carry no logical content.

Unlike every gate before it, this one is not reproducing a recorded answer from a
recorded answer: the goal is derived from the `.bum` alone.

Rodin keeps a sequent's hypotheses in a parent chain of predicate sets, so the whole
chain has to be resolved before they can be compared. -/
private def refName (ref : String) : String :=
  ((ref.splitOn "#").getLast!).replace "\\/" "/"
    |>.replace "\\\\" "\\"
    |>.replace "\\|" "|"

private partial def predicateSets (e : XmlElem) : List (String × Option String × List String) :=
  let here :=
    if e.tag == "org.eventb.core.poPredicateSet" then
      [(((e.attr? "name").getD ""),
        (e.attr? "org.eventb.core.parentSet").map refName,
        e.children.filter (fun c => c.tag == "org.eventb.core.poPredicate")
          |>.filterMap (fun c => c.attr? "org.eventb.core.predicate"))]
    else []
  e.children.foldl (fun acc c => acc ++ predicateSets c) here

private def chainHyps (sets : List (String × Option String × List String))
    (start : Option String) : List String :=
  go sets.length start []
where
  go : Nat → Option String → List String → List String
    | 0, _, acc => acc
    | _, none, acc => acc
    | fuel + 1, some n, acc =>
      match sets.find? (fun s => s.1 == n) with
      | none => acc
      | some (_, parent, preds) => go fuel parent (preds ++ acc)

private partial def goldHyps (e : XmlElem)
    (sets : List (String × Option String × List String)) : List (String × List String) :=
  let here :=
    if e.tag == "org.eventb.core.poSequent" then
      match e.attr? "name" with
      | some n =>
        let inner := e.children.find? (fun c => c.tag == "org.eventb.core.poPredicateSet")
        let parent := inner.bind (fun i =>
          (i.attr? "org.eventb.core.parentSet").map refName)
        [(n, chainHyps sets parent)]
      | none => []
    else []
  e.children.foldl (fun acc c => acc ++ goldHyps c sets) here

private partial def goldGoals (e : XmlElem) : List (String × String) :=
  let here :=
    if e.tag == "org.eventb.core.poSequent" then
      match e.attr? "name" with
      | some n =>
        -- Most sequents put the goal directly under the sequent. Rodin stores WFIS
        -- in its witness predicate set, whose sole predicate is the goal.
        let direct := e.children.filter (fun c => c.tag == "org.eventb.core.poPredicate")
          |>.filterMap (fun c => c.attr? "org.eventb.core.predicate")
        let witness := if n.endsWith "/WFIS" then
          (e.children.find? (fun c => c.tag == "org.eventb.core.poPredicateSet")).toList
            |>.flatMap (fun set => set.children.filter
              (fun c => c.tag == "org.eventb.core.poPredicate")
              |>.filterMap (fun c => c.attr? "org.eventb.core.predicate"))
        else []
        match (direct ++ witness).getLast? with
        | some g => [(n, g)]
        | none => []
      | none => []
    else []
  e.children.foldl (fun acc c => acc ++ goldGoals c) here

private def readGoldGoals (path : System.FilePath) : IO (List (String × String)) := do
  match parseXml (← IO.FS.readBinFile path) with
  | .error _ => return []
  | .ok xml => return goldGoals xml

/-- Ascriptions carry no logical content, so a generator has no reason to reproduce
them. Nothing else is normalised: the gate's job is to notice a difference, and a
comparison that rewrites both sides can only hide one. -/
private def comparable (t : Term) : Term := Formula.stripAscriptions t

private def equivalent (left right : Term) : Bool :=
  Formula.alphaEq (comparable left) (comparable right)

private structure GoalResult where
  key    : String
  status : String

private structure CoverageResult where
  component : String
  kind : String
  name : String
  derivation : String
  reason : String
  diagnostic : String

private def coverageReasonFor (hasName hasGoal derived goalOK hypsOK : Bool) : String :=
  if !hasName then "no-sequent"
  else if !derived then "matched"
  else if !hasGoal then "no-sequent"
  else if !goalOK then "goal-differs"
  else if !hypsOK then "hypotheses-differ"
  else "matched"

private theorem deletedGoldSequentIsCoverageLoss :
    coverageReasonFor false false false false false == "no-sequent" := by decide

private def isPlainTypeInvariant : Formula.Term → Bool
  | .bin op (.id _) (.id _) => op == "∈" || op == "⊆"
  | .bin op (.id _) (.pre "ℙ" (.id _)) => op == "∈"
  | _ => false

private def omittedInvariant (project : Project) (file name : String) : Bool :=
  match lookupComponent project file, name.splitOn "/" with
  | some component, _ :: label :: _ =>
      match component.elem.children.find? (fun elem =>
          elem.tag == "org.eventb.core.invariant" &&
          elem.attr? "org.eventb.core.label" == some label) with
      | some invariant =>
          match invariant.attr? "org.eventb.core.predicate" with
          | some predicate =>
              match Formula.parse predicate with
              | .ok term => isPlainTypeInvariant term
              | .error _ => false
          | none => false
      | none => false
  | _, _ => false

private def coverageDiagnostic (project : Project) (file : String)
    (obligation : Obligation) (reason : String) : String :=
  if reason != "no-sequent" then "none"
  else if obligation.kind == "INV" && omittedInvariant project file obligation.name then
    "pinned-bpo-omits-plain-type-invariant"
  else
    match obligation.kind with
    | "WD" => "pinned-bpo-omits-definedness-sequent"
    | "GRD" => "pinned-bpo-omits-refinement-guard-sequent"
    | "SIM" => "pinned-bpo-omits-refinement-action-sequent"
    | "WFIS" => "pinned-bpo-omits-witness-feasibility-sequent"
    | _ => "pinned-bpo-omits-sequent"

#guard isPlainTypeInvariant (.bin "⊆" (.id "x") (.id "S"))
#guard isPlainTypeInvariant (.bin "∈" (.id "x") (.pre "ℙ" (.id "S")))
#guard !isPlainTypeInvariant (.bin "=" (.id "x") (.id "y"))

private def goalAgrees (obligation : Obligation) (gold : List (String × String)) : Bool :=
  match obligation.goal, gold.find? (fun p => p.1 == obligation.name) with
  | some ours, some (_, wanted) =>
      match Formula.parse wanted with
      | .ok theirs => equivalent ours theirs
      | .error _ => false
  | _, _ => false

private def hypothesesAgree (obligation : Obligation)
    (gold : List (String × List String)) : Bool :=
  match gold.find? (fun p => p.1 == obligation.name) with
  | none => false
  | some (_, wanted) =>
      let want := wanted.filterMap (fun text => (Formula.parse text).toOption.map comparable)
      let ours := obligation.hyps.map comparable
      let missing := want.filter (fun w => !ours.any (equivalent w ·))
      let extra := ours.filter (fun h => !want.any (equivalent h ·))
      missing.isEmpty && extra.isEmpty

private def coverage (project : Project) (file : String) (names : List String)
    (goals : List (String × String)) (hyps : List (String × List String)) :
    List CoverageResult :=
  (generate project file).map fun obligation =>
    let hasName := names.contains obligation.name
    let hasGoal := goals.any (fun p => p.1 == obligation.name)
    let derived := obligation.goal.isSome
    let goalOK := goalAgrees obligation goals
    let hypsOK := hypothesesAgree obligation hyps
    { component := file
      kind := obligation.kind
      name := obligation.name
      derivation := if derived then "derived" else "not-derived"
      reason := coverageReasonFor hasName hasGoal derived goalOK hypsOK
      diagnostic := coverageDiagnostic project file obligation
        (coverageReasonFor hasName hasGoal derived goalOK hypsOK) }

private def coverageLine (record : CoverageResult) : String :=
  String.intercalate "\t"
    [record.component, record.kind, record.name, record.derivation, record.reason,
      record.diagnostic]

private def coverageHistogram (records : List CoverageResult) : List (String × Nat) :=
  (records.foldl
    (fun counts record =>
      if record.reason == "matched" then counts
      else histogramAdd
        (record.reason ++ "\t" ++ record.diagnostic ++ "\t" ++ record.component ++
          "\t" ++ record.kind) counts)
    []).mergeSort (fun left right =>
    if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)

private def compatibilityDiagnosticNames : List String :=
  ["pinned-bpo-omits-plain-type-invariant",
   "pinned-bpo-omits-definedness-sequent",
   "pinned-bpo-omits-refinement-guard-sequent",
   "pinned-bpo-omits-refinement-action-sequent",
   "pinned-bpo-omits-witness-feasibility-sequent"]

private def isKnownCompatibilityRecord (record : CoverageResult) : Bool :=
  record.reason == "no-sequent" && compatibilityDiagnosticNames.contains record.diagnostic

private def compatibilityRecords (records : List CoverageResult) : List CoverageResult :=
  records.filter (fun record => record.reason == "no-sequent")

#guard coverageReasonFor true true true false true == "goal-differs"
#guard coverageReasonFor true true true true false == "hypotheses-differ"
#guard compatibilityDiagnosticNames.contains "pinned-bpo-omits-definedness-sequent"
#guard !compatibilityDiagnosticNames.contains "pinned-bpo-omits-sequent"

/-- Only obligations we generate a goal for are scored; the rest are not yet attempted
and would otherwise drown the signal. -/
private def checkGoals (project : Project) (file : String)
    (gold : List (String × String)) : List GoalResult :=
  (generate project file).filterMap fun o =>
    match o.goal with
    | none => none
    | some g =>
      let key := file ++ "\t" ++ o.name
      match gold.find? (fun p => p.1 == o.name) with
      | none =>
          -- The name gate records a generated PO absent from Rodin's file. There is
          -- no WFIS statement to compare here; avoid counting that coverage gap twice.
          if o.kind == "WFIS" then none
          else some { key := key, status := "FAIL:no such sequent in .bpo" }
      | some (_, gs) =>
        match Formula.parse gs with
        | .error _ => some { key := key, status := "FAIL:gold goal unparsable" }
        | .ok gt =>
          if Formula.alphaEq (Formula.stripAscriptions gt) (Formula.stripAscriptions g) then
            some { key := key, status := "PASS" }
          else
            some { key := key, status := "FAIL:differs" }

private def readGoldHyps (path : System.FilePath) : IO (List (String × List String)) := do
  match parseXml (← IO.FS.readBinFile path) with
  | .error _ => return []
  | .ok xml => return goldHyps xml (predicateSets xml)

/-- Hypotheses are scored as sets: Rodin's order is an artefact of how it walks the
predicate-set chain, and a generator that produces the same assumptions in a different
order is not wrong. -/
private def checkHyps (project : Project) (file : String)
    (gold : List (String × List String)) : List GoalResult :=
  (generate project file).filterMap fun o =>
    -- Scored for every obligation with a derived goal. An empty hypothesis list is a
    -- claim (INITIALISATION assumes nothing), not an absence of one.
    if o.goal.isNone then none else
    let key := file ++ "\t" ++ o.name
    match gold.find? (fun p => p.1 == o.name) with
    | none =>
        if o.kind == "WFIS" then none
        else some { key := key, status := "FAIL:no such sequent in .bpo" }
    | some (_, gs) =>
      let want := gs.filterMap (fun t => (Formula.parse t).toOption.map comparable)
      let ours := o.hyps.map comparable
      let missing := want.filter (fun w => !ours.any (equivalent w ·))
      let extra := ours.filter (fun h => !want.any (equivalent h ·))
      if missing.isEmpty && extra.isEmpty then some { key := key, status := "PASS" }
      else some { key := key,
                  status := s!"FAIL:missing {missing.length} extra {extra.length}" }

private structure P4Result where
  obligation : Obligation
  result : Result
  accepted : Bool

private def localResults (project : Project) (poResults : List PoResult) : List P4Result :=
  let matched := poResults.filter (·.status == "PASS") |>.map (·.key)
  let obligations := (project.flatMap fun component => generate project component.name).filter
    fun obligation => matched.contains (obligation.component ++ "\t" ++ obligation.name)
  let ledger := Trust.Ledger.ofObligations obligations
  obligations.map fun obligation =>
    let result := prove obligation
    let accepted := match attach ledger obligation result with
      | .ok _ => result.discharged
      | .error _ => false
    { obligation, result, accepted }

private def goalHistogram (results : List GoalResult) : List (String × Nat) :=
  (results.foldl
    (fun counts r => if r.status.startsWith "FAIL:" then histogramAdd r.status counts
                     else counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)

private def termShape : Term → String
  | .id _ => "id"
  | .num _ => "numeral"
  | .bin op _ _ => "bin:" ++ op
  | .pre op _ => "pre:" ++ op
  | .post op _ => "post:" ++ op
  | .app _ _ => "application"
  | .img _ _ => "image"
  | .set _ => "set"
  | .bind op _ _ => "binder:" ++ op

private def p4Histogram (results : List P4Result) : List (String × Nat) :=
  (results.foldl (fun counts result =>
    if result.accepted then counts
    else histogramAdd (match result.obligation.goal with
      | some goal => termShape goal
      | none => "no-goal") counts) []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)

private def nonemptyLines (source : String) : List String :=
  source.splitOn "\n" |>.filter (fun line => !line.isEmpty)

private def baselineDiff (baseline actual : List String) : IO Bool := do
  if baseline == actual then
    pure true
  else
    IO.eprintln "parse baseline mismatch:"
    for line in actual do
      if !baseline.contains line then
        IO.eprintln s!"+ {line}"
    for line in baseline do
      if !actual.contains line then
        IO.eprintln s!"- {line}"
    pure false

private def writeBaseline (path : String) (lines : List String) : IO Unit := do
  IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")

private def writeStatus (results : List FileResult) (formulas : List FormulaResult)
    (types : List TypeResult) (pos : List PoResult) (goals hyps : List GoalResult)
    (compatibilityCount : Nat) (p4 : List P4Result) (inventory : List (String × Nat)) :
    IO Unit := do
  let passed := results.countP (fun result => result.status == "PASS")
  let fpass := formulas.countP (fun result => result.status == "PASS")
  let tpass := types.countP (fun result => result.status == "PASS")
  let ppass := pos.countP (fun result => result.status == "PASS")
  let gpass := goals.countP (fun result => result.status == "PASS")
  let hpass := hyps.countP (fun result => result.status == "PASS")
  let p4pass := p4.countP (·.accepted)
  let counts := inventory.map (fun (name, count) => s!"| {name} | {count} |")
  IO.FS.writeFile "STATUS.md"
    ("# STATUS\n\nGenerated by `lake exe gates --status`. Do not edit; see AGENTS.md " ++
      "rule 1.\n\n| Phase | Gate | Actual | Target |\n| --- | --- | --- | --- |\n" ++
      s!"| P0 reader | files read losslessly | {passed}/{results.length} | " ++
        s!"{results.length} |\n" ++
      s!"| P1 formula parser | formulas parsed and round-tripped | {fpass}/{formulas.length}" ++
        s!" | {formulaCount} |\n" ++
      s!"| P2 typechecker | `.bpo` identifier types reproduced | {tpass}/{types.length}" ++
        s!" | {typeCount} |\n" ++
      s!"| P3 POG | `.bpo` PO sequents reproduced | {ppass}/{sequentCount} |" ++
        s!" {sequentCount} |\n" ++
      s!"| P3b statements | goals derived | {gpass}/{goals.length} | tracked |\n" ++
      s!"| P3b hypotheses | hypotheses derived | {hpass}/{hyps.length} | tracked |\n" ++
      s!"| P3b compatibility | pinned omissions | {compatibilityCount} | tracked |\n" ++
      s!"| P4 provers | local evidence vs Rodin `.bps` | {p4pass}/{p4.length} |" ++
        " measured evidence baseline |\n" ++
      "\n## Trust ledger\n\nThe artifact Rodin cannot produce: for each obligation, " ++
      "what is actually holding it\nup. This status includes only evidence accepted " ++
      "through the local ledger; it is not kernel proof.\n\n" ++
      "| status | count |\n| --- | --- |\n" ++
      s!"| kernel-checked | 0 |\n| smt-trusted | 0 |\n" ++
      s!"| rodin-imported | 0 |\n| external-trusted | {p4pass} |\n" ++
      s!"| unproved | {p4.length - p4pass} |\n\n" ++
      s!"Rodin discharged all {rodinAuto + rodinManual} of its obligations: " ++
      s!"{rodinAuto} automatically, {rodinManual} by hand.\n" ++
      "\n## Element census\n\nSummed over every corpus source file. A reader that " ++
      "silently dropped an element would\nshow up here as a shortfall, which a per-file " ++
      "PASS/FAIL cannot detect.\n\n| element | count |\n| --- | --- |\n" ++
      String.intercalate "\n" counts ++ "\n")

private def run (args : List String) : IO UInt32 := do
  let files ← sourceFiles
  let mut acc : List FileResult := []
  for path in files do
    acc := (← checkFile path) :: acc
  let results := acc.reverse
  let actual := results.map (fun result => result.path ++ "\t" ++ result.status)
  let inventory := totalInventory results
  let filesPassed := results.countP (fun result => result.status == "PASS")
  let inventoryOK := inventory == expectedInventory
  let project : Project := results.filterMap fun r =>
    r.model.map fun m =>
      { name := ((r.path.splitOn "/").getLast!.splitOn ".").head!, elem := m.root }
  let mut typeResults : List TypeResult := []
  for path in files do
    let bpo := (path.toString.dropEnd 4).toString ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    let gold ← readGoldTypes bpo
    typeResults := typeResults ++ checkTypes project name gold
  let typePassed := typeResults.countP (fun r => r.status == "PASS")
  let typeActual := typeResults.map (fun r => r.key ++ "\t" ++ r.status)
  let mut poResults : List PoResult := []
  for path in files do
    let bpo := (path.toString.dropEnd 4).toString ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    poResults := poResults ++ checkPOs project name (← readGoldPOs bpo)
  let mut goalResults : List GoalResult := []
  for path in files do
    let bpo := (path.toString.dropEnd 4).toString ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    goalResults := goalResults ++ checkGoals project name (← readGoldGoals bpo)
  let mut hypResults : List GoalResult := []
  for path in files do
    let bpo := (path.toString.dropEnd 4).toString ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    hypResults := hypResults ++ checkHyps project name (← readGoldHyps bpo)
  let mut coverageResults : List CoverageResult := []
  for path in files do
    let bpo := (path.toString.dropEnd 4).toString ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    let names ← readGoldPOs bpo
    let goals ← readGoldGoals bpo
    let hyps ← readGoldHyps bpo
    coverageResults := coverageResults ++ coverage project name names goals hyps
  let hypPassed := hypResults.countP (fun r => r.status == "PASS")
  let hypActual := hypResults.map (fun r => r.key ++ "\t" ++ r.status)
  let goalPassed := goalResults.countP (fun r => r.status == "PASS")
  let goalActual := goalResults.map (fun r => r.key ++ "\t" ++ r.status)
  let poPassed := poResults.countP (fun r => r.status == "PASS")
  let p4Results := localResults project poResults
  let p4Passed := p4Results.countP (·.accepted)
  let poActual := poResults.map (fun r => r.key ++ "\t" ++ r.status)
  let compatibility := compatibilityRecords coverageResults
  let compatibilityActual := compatibility.map coverageLine
  let compatibilityOK := coverageResults.all (fun record =>
    record.reason == "matched" || isKnownCompatibilityRecord record)
  let formulas := formulaResults results
  let formulaPassed := formulas.countP (fun result => result.status == "PASS")
  let formulaActual := formulas.map (fun result => result.key ++ "\t" ++ result.status)
  let formulaCountOK := formulas.length == formulaCount
  IO.println s!"P0 reader: {filesPassed}/{results.length}"
  IO.println s!"P1 formulas: {formulaPassed}/{formulas.length}"
  IO.println s!"P2 types: {typePassed}/{typeResults.length}"
  if typeResults.length != typeCount then
    IO.eprintln s!"type assertion count {typeResults.length}, expected {typeCount}"
  IO.println s!"P3 obligations: {poPassed}/{sequentCount}"
  IO.println s!"P3b statements: {goalPassed}/{goalResults.length} derived"
  IO.println s!"P3b hypotheses: {hypPassed}/{hypResults.length} derived"
  IO.println s!"P3b compatibility: {compatibility.length} pinned omissions"
  IO.println s!"P4 local baseline: {p4Passed}/{p4Results.length} discharged"
  if !compatibilityOK then
    IO.eprintln "unclassified P3b compatibility diagnostic"
  if !formulaCountOK then
    IO.eprintln s!"formula count {formulas.length}, expected {formulaCount}"
  if !inventoryOK then
    IO.eprintln s!"element inventory mismatch: {inventory}"
  if args.contains "--histogram" then
    for (reason, count) in histogram results do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in formulaHistogram formulas do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in typeHistogram typeResults do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in poHistogram poResults do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in goalHistogram goalResults do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in goalHistogram hypResults do
      IO.println s!"{count}\t{reason}"
    for (shape, count) in p4Histogram p4Results do
      IO.println s!"{count}\tP4\t{shape}"
    for (reason, count) in coverageHistogram coverageResults do
      IO.println s!"{count}\tP3b\t{reason}"
  if args.contains "--coverage" then
    IO.println "component\tkind\tname\tderivation\treason\tdiagnostic"
    for record in coverageResults do
      IO.println (coverageLine record)
  if args.contains "--status" then
    writeStatus results formulas typeResults poResults goalResults hypResults compatibility.length
      p4Results inventory
  let parseOK := results.all (fun result => result.status == "PASS")
  if args.contains "--bless" then
    -- P0 must be perfect to bless, since a dropped file would silently shrink the P1
    -- denominator. P1 blesses whatever it currently reaches: that is the ratchet.
    if parseOK && inventoryOK && formulaCountOK && compatibilityOK then
      writeBaseline "baseline/parse.tsv" actual
      writeBaseline "baseline/formula.tsv" formulaActual
      writeBaseline "baseline/typecheck.tsv" typeActual
      writeBaseline "baseline/pog.tsv" poActual
      writeBaseline "baseline/statement.tsv" goalActual
      writeBaseline "baseline/hypothesis.tsv" hypActual
      writeBaseline "baseline/compatibility.tsv" compatibilityActual
    else
      IO.eprintln "refusing to bless a failed P0 gate"
      return 1
    return 0
  let baseline ← try IO.FS.readFile "baseline/parse.tsv" catch _ => pure ""
  let baselineOK ← baselineDiff (nonemptyLines baseline) actual
  let fbaseline ← try IO.FS.readFile "baseline/formula.tsv" catch _ => pure ""
  let fbaselineOK ← baselineDiff (nonemptyLines fbaseline) formulaActual
  let tbaseline ← try IO.FS.readFile "baseline/typecheck.tsv" catch _ => pure ""
  let tbaselineOK ← baselineDiff (nonemptyLines tbaseline) typeActual
  let pbaseline ← try IO.FS.readFile "baseline/pog.tsv" catch _ => pure ""
  let pbaselineOK ← baselineDiff (nonemptyLines pbaseline) poActual
  let gbaseline ← try IO.FS.readFile "baseline/statement.tsv" catch _ => pure ""
  let gbaselineOK ← baselineDiff (nonemptyLines gbaseline) goalActual
  let hbaseline ← try IO.FS.readFile "baseline/hypothesis.tsv" catch _ => pure ""
  let hbaselineOK ← baselineDiff (nonemptyLines hbaseline) hypActual
  let cbaseline ← try IO.FS.readFile "baseline/compatibility.tsv" catch _ => pure ""
  let cbaselineOK ← baselineDiff (nonemptyLines cbaseline) compatibilityActual
  if !baselineOK || !fbaselineOK || !tbaselineOK || !pbaselineOK || !gbaselineOK
      || !hbaselineOK || !cbaselineOK || !compatibilityOK then
    return 1
  if parseOK && inventoryOK && formulaCountOK then
    if p4Results.length == sequentCount then return 0 else return 1
  return 1

end EventB.Gates

-- Must sit at the top level: `lean_exe gates` links against `main`, not
-- `EventB.Gates.main`.
def main (args : List String) : IO UInt32 := EventB.Gates.run args
