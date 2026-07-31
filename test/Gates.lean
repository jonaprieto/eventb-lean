import EventB.Model
import EventB.Formula.Parse
import EventB.Typing.Check
import EventB.POG

namespace EventB.Gates

open EventB
open EventB.Formula
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
        pure { path := path.toString, status := "FAIL:" ++ shortReason reason }
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
  | .error reason => { key := key, status := "FAIL:" ++ reason }
  | .ok term =>
      match Formula.parse (Formula.print term) with
      | .error reason => { key := key, status := "FAIL:reprint " ++ reason }
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
  | .error e => gold.map (fun (n, _) => { key := file ++ "\t" ++ n, status := "FAIL:" ++ e })
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
private partial def predicateSets (e : XmlElem) : List (String × Option String × List String) :=
  let here :=
    if e.tag == "org.eventb.core.poPredicateSet" then
      [(((e.attr? "name").getD ""),
        (e.attr? "org.eventb.core.parentSet").map (fun t => (t.splitOn "#").getLast!),
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
          (i.attr? "org.eventb.core.parentSet").map (fun t => (t.splitOn "#").getLast!))
        [(n, chainHyps sets parent)]
      | none => []
    else []
  e.children.foldl (fun acc c => acc ++ goldHyps c sets) here

private partial def goldGoals (e : XmlElem) : List (String × String) :=
  let here :=
    if e.tag == "org.eventb.core.poSequent" then
      match e.attr? "name" with
      | some n =>
        -- The sequent's own predicates are the goal; the last one is the statement.
        match (e.children.filter (fun c => c.tag == "org.eventb.core.poPredicate")
                |>.filterMap (fun c => c.attr? "org.eventb.core.predicate")).getLast? with
        | some g => [(n, g)]
        | none => []
      | none => []
    else []
  e.children.foldl (fun acc c => acc ++ goldGoals c) here

private def readGoldGoals (path : System.FilePath) : IO (List (String × String)) := do
  match parseXml (← IO.FS.readBinFile path) with
  | .error _ => return []
  | .ok xml => return goldGoals xml

private structure GoalResult where
  key    : String
  status : String

/-- Only obligations we generate a goal for are scored; the rest are not yet attempted
and would otherwise drown the signal. -/
private def checkGoals (project : Project) (file : String)
    (gold : List (String × String)) : List GoalResult :=
  (generate project file).filterMap fun o =>
    o.goal.map fun g =>
      let key := file ++ "\t" ++ o.name
      match gold.find? (fun p => p.1 == o.name) with
      | none => { key := key, status := "FAIL:no such sequent in .bpo" }
      | some (_, gs) =>
        match Formula.parse gs with
        | .error _ => { key := key, status := "FAIL:gold goal unparsable" }
        | .ok gt =>
          if Formula.stripAscriptions gt == Formula.stripAscriptions g then
            { key := key, status := "PASS" }
          else
            { key := key, status := "FAIL:differs" }

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
    if o.hyps.isEmpty then none else
    let key := file ++ "\t" ++ o.name
    match gold.find? (fun p => p.1 == o.name) with
    | none => some { key := key, status := "FAIL:no such sequent in .bpo" }
    | some (_, gs) =>
      let want := gs.filterMap (fun t => (Formula.parse t).toOption.map Formula.stripAscriptions)
      let ours := o.hyps.map Formula.stripAscriptions
      let missing := want.filter (fun w => !ours.contains w)
      let extra := ours.filter (fun h => !want.contains h)
      if missing.isEmpty && extra.isEmpty then some { key := key, status := "PASS" }
      else some { key := key,
                  status := s!"FAIL:missing {missing.length} extra {extra.length}" }

private def goalHistogram (results : List GoalResult) : List (String × Nat) :=
  (results.foldl
    (fun counts r => if r.status.startsWith "FAIL:" then histogramAdd r.status counts
                     else counts)
    []).mergeSort (fun left right =>
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
    (types : List TypeResult) (pos : List PoResult) (inventory : List (String × Nat)) :
    IO Unit := do
  let passed := results.countP (fun result => result.status == "PASS")
  let fpass := formulas.countP (fun result => result.status == "PASS")
  let tpass := types.countP (fun result => result.status == "PASS")
  let ppass := pos.countP (fun result => result.status == "PASS")
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
      s!"| P4 provers | discharge rate vs Rodin `.bps` | 0/{sequentCount} |" ++
        s!" within 20pt of {rodinAuto} |\n" ++
      "\n## Trust ledger\n\nThe artifact Rodin cannot produce: for each obligation, " ++
      "what is actually holding it\nup. Empty of proofs until P4, but the accounting " ++
      "is in place, and the two soundness\ntheorems it will rest on are already " ++
      "axiom-free (`Proved.sound`, `Refines.sound`,\nchecked in CI).\n\n" ++
      "| status | count |\n| --- | --- |\n" ++
      s!"| kernel-checked | 0 |\n| smt-trusted | 0 |\n| atelierb-trusted | 0 |\n" ++
      s!"| unproved | {ppass} |\n\n" ++
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
    let bpo := path.toString.dropRight 4 ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    let gold ← readGoldTypes bpo
    typeResults := typeResults ++ checkTypes project name gold
  let typePassed := typeResults.countP (fun r => r.status == "PASS")
  let typeActual := typeResults.map (fun r => r.key ++ "\t" ++ r.status)
  let mut poResults : List PoResult := []
  for path in files do
    let bpo := path.toString.dropRight 4 ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    poResults := poResults ++ checkPOs project name (← readGoldPOs bpo)
  let mut goalResults : List GoalResult := []
  for path in files do
    let bpo := path.toString.dropRight 4 ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    goalResults := goalResults ++ checkGoals project name (← readGoldGoals bpo)
  let mut hypResults : List GoalResult := []
  for path in files do
    let bpo := path.toString.dropRight 4 ++ ".bpo"
    let name := ((path.toString.splitOn "/").getLast!.splitOn ".").head!
    hypResults := hypResults ++ checkHyps project name (← readGoldHyps bpo)
  let hypPassed := hypResults.countP (fun r => r.status == "PASS")
  let hypActual := hypResults.map (fun r => r.key ++ "\t" ++ r.status)
  let goalPassed := goalResults.countP (fun r => r.status == "PASS")
  let goalActual := goalResults.map (fun r => r.key ++ "\t" ++ r.status)
  let poPassed := poResults.countP (fun r => r.status == "PASS")
  let poActual := poResults.map (fun r => r.key ++ "\t" ++ r.status)
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
  if args.contains "--status" then
    writeStatus results formulas typeResults poResults inventory
  let parseOK := results.all (fun result => result.status == "PASS")
  if args.contains "--bless" then
    -- P0 must be perfect to bless, since a dropped file would silently shrink the P1
    -- denominator. P1 blesses whatever it currently reaches: that is the ratchet.
    if parseOK && inventoryOK && formulaCountOK then
      writeBaseline "baseline/parse.tsv" actual
      writeBaseline "baseline/formula.tsv" formulaActual
      writeBaseline "baseline/typecheck.tsv" typeActual
      writeBaseline "baseline/pog.tsv" poActual
      writeBaseline "baseline/statement.tsv" goalActual
      writeBaseline "baseline/hypothesis.tsv" hypActual
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
  if !baselineOK || !fbaselineOK || !tbaselineOK || !pbaselineOK || !gbaselineOK
      || !hbaselineOK then
    return 1
  if parseOK && inventoryOK && formulaCountOK then
    return 0
  return 1

end EventB.Gates

-- Must sit at the top level: `lean_exe gates` links against `main`, not
-- `EventB.Gates.main`.
def main (args : List String) : IO UInt32 := EventB.Gates.run args
