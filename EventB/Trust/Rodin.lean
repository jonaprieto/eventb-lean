/- Rodin proof-status import, kept separate from kernel replay. -/

import EventB.Trust
import EventB.Xml

namespace EventB.Trust.Rodin

open EventB

structure Status where
  name : String
  confidence : Nat
  manual : Bool
  deriving BEq, Repr, Inhabited

def Status.discharged (status : Status) : Bool := status.confidence > 0

structure Provenance where
  model : String
  bpo : String
  statuses : String
  deriving BEq, Repr, Inhabited

structure Comparison where
  expected : Nat
  discharged : Nat
  automatic : Nat
  manual : Nat
  missing : Nat
  stale : Nat
  /-- True when the caller compared multiple component scopes against an unscoped
  proof-status artifact; names alone cannot safely identify those obligations. -/
  scopeAmbiguous : Bool := false
  deriving BEq, Repr, Inhabited

private def attr (elem : XmlElem) (name : String) : Except String String :=
  match elem.attr? name with
  | some value => pure value
  | none => .error s!"missing `{name}` on `{elem.tag}`"

private def natValue (source : String) : Option Nat :=
  if source.isEmpty then none
  else
    source.toList.foldl (fun result char => do
      let value ← result
      let digit := char.toNat
      if 48 ≤ digit && digit ≤ 57 then some (value * 10 + digit - 48) else none) (some 0)

private def parseStatus (elem : XmlElem) : Except String Status := do
  unless elem.tag == "org.eventb.core.psStatus" do
    throw s!"unsupported proof-status child `{elem.tag}`"
  unless elem.children.isEmpty do
    throw s!"proof-status `{elem.tag}` must not have children"
  let name ← attr elem "name"
  unless !name.isEmpty do
    throw "proof-status name must not be empty"
  let confidenceSource ← attr elem "org.eventb.core.confidence"
  let confidence ← match natValue confidenceSource with
    | some value => pure value
    | none => .error s!"invalid confidence `{confidenceSource}`"
  unless confidence > 0 do
    throw "proof-status confidence must be positive"
  let manual ← match elem.attr? "org.eventb.core.psManual" with
    | some "true" => pure true
    | some "false" => pure false
    | some value => .error s!"invalid psManual `{value}`"
    | none => .error "missing `org.eventb.core.psManual` on proof-status"
  pure { name, confidence, manual }

def validateStatuses (statuses : List Status) : Except EventB.Error Unit :=
  let rec go : List Status → Except EventB.Error Unit
    | [] => pure ()
    | status :: rest =>
        if status.name.isEmpty then
          .error (EventB.Error.trust "proof-status name must not be empty")
        else if status.confidence == 0 then
          .error (EventB.Error.trust
            s!"proof-status `{status.name}` has zero confidence")
        else if rest.any (·.name == status.name) then
          .error (EventB.Error.trust
            s!"duplicate proof-status `{status.name}`")
        else
          go rest
  go statuses

def importStatuses (source : String) : Except EventB.Error (List Status) := do
  let root ← match parseXmlString source with
    | .ok root => pure root
    | .error error => .error (EventB.Error.trust
        s!"invalid Rodin proof-status XML: {error.pretty source.toUTF8}")
  unless root.tag == "org.eventb.core.psFile" do
    throw (EventB.Error.trust s!"root is not a proof-status file: `{root.tag}`")
  let statuses ← (root.children.mapM parseStatus).mapError EventB.Error.trust
  validateStatuses statuses
  pure statuses

private def status? (statuses : List Status) (name : String) : Option Status :=
  statuses.find? (·.name == name)

private def duplicateKeys (seen : List String) : List String → List String
  | [] => []
  | key :: rest =>
      if seen.contains key then key :: duplicateKeys seen rest
      else duplicateKeys (key :: seen) rest

def provenanceDigest (provenance : Provenance) : String :=
  s!"eventb-v2-{String.hash
    (provenance.model ++ "\n" ++ provenance.bpo ++ "\n" ++ provenance.statuses)}"

def compare (obligations : List POG.Obligation) (statuses : List Status) : Comparison :=
  let eligible := obligations.filter fun obligation =>
    obligation.diagnostics.isEmpty && obligation.goal.isSome
  let expected := eligible.map (·.name)
  let duplicateExpected := duplicateKeys [] (eligible.map fun obligation =>
    obligation.component ++ "\t" ++ obligation.name)
  let duplicateStatuses := duplicateKeys [] (statuses.map (·.name))
  let scopeAmbiguous := (eligible.map (·.component)).eraseDups.length > 1 ||
    !duplicateExpected.isEmpty || !duplicateStatuses.isEmpty
  let present := if scopeAmbiguous then [] else eligible.filterMap fun obligation =>
    match status? statuses obligation.name with
    | some status => if status.discharged then some (obligation.name, status) else none
    | none => none
  { expected := eligible.length
    discharged := present.length
    automatic := present.countP (·.2.manual == false)
    manual := present.countP (·.2.manual)
    missing := if scopeAmbiguous then eligible.length
      else eligible.countP (status? statuses ·.name |>.isNone)
    scopeAmbiguous := scopeAmbiguous
    stale := statuses.countP (fun status => !expected.contains status.name) }

private def attachVerified (ledger : Ledger) (obligation : POG.Obligation)
    (provenance : Provenance) (manual : Bool) : Except EventB.Error Ledger := do
  ledger.validate
  let evidence := .rodinImportedProvenance provenance.model provenance.bpo provenance.statuses
    (provenanceDigest provenance) manual
  if !obligation.diagnostics.isEmpty then
    .error (EventB.Error.trust "cannot attach Rodin evidence to an obligation with diagnostics")
  else if obligation.goal.isNone then
    .error (EventB.Error.trust "cannot attach Rodin evidence to a statement-less obligation")
  else if ledger.entry? obligation.component obligation.name |>.isNone then
    .error (EventB.Error.trust s!"obligation `{obligation.name}` is not in the ledger")
  else if ledger.entries.countP (fun entry =>
      entry.component == obligation.component && entry.obligation == obligation.name) != 1 then
    .error (EventB.Error.trust s!"ledger has duplicate entries for `{obligation.name}`")
  else
    let entry := ledger.entry? obligation.component obligation.name |>.get!
    if !entry.isConsistent then
      .error (EventB.Error.trust
        s!"ledger entry for `{obligation.component}:{obligation.name}` is internally inconsistent")
    else if entry.canonical != obligation.canonical then
      .error (EventB.Error.trust "Rodin evidence canonical mismatch")
    else if entry.fingerprint != Trust.fingerprint obligation.canonical then
      .error (EventB.Error.trust "Rodin evidence fingerprint mismatch")
    else if entry.mode != .unproved && Mode.rank .rodinImported <= Mode.rank entry.mode then
      .error (EventB.Error.trust
        s!"Rodin evidence cannot replace `{obligation.component}:{obligation.name}`")
    else
      .ok { entries := ledger.entries.map fun current =>
        if current.component == obligation.component && current.obligation == obligation.name then
          { current with mode := .rodinImported, evidence := evidence }
        else current }

private def rootModel (source : String) : Except EventB.Error (String × String) := do
  let root ← match parseXmlString source with
    | .ok root => pure root
    | .error error => .error (EventB.Error.trust
        s!"invalid model XML: {error.pretty source.toUTF8}")
  unless root.tag == "org.eventb.core.machineFile" ||
      root.tag == "org.eventb.core.contextFile" do
    throw (EventB.Error.trust s!"unsupported Rodin model root `{root.tag}`")
  match root.attr? "org.eventb.core.name" with
  | some name => pure (name, root.tag)
  | none => .error (EventB.Error.trust "model XML has no component name")

private partial def findPoSequent (elem : XmlElem) (name : String) : Option XmlElem :=
  if elem.tag == "org.eventb.core.poSequent" && elem.attr? "name" == some name then
    some elem
  else
    match elem.children.filterMap (fun child => findPoSequent child name) with
    | first :: _ => some first
    | [] => none

private def predicateTexts (elem : XmlElem) : List String :=
  elem.children.filterMap fun child =>
    if child.tag == "org.eventb.core.poPredicate" then
      child.attr? "org.eventb.core.predicate"
    else none

private def sequentGoal (name : String) (sequent : XmlElem) : Option String :=
  let direct := predicateTexts sequent
  let witness := if name.endsWith "/WFIS" then
      sequent.children.filter (fun child => child.tag == "org.eventb.core.poPredicateSet")
        |>.flatMap predicateTexts
    else []
  (direct ++ witness).getLast?

private structure PredicateSet where
  name : String
  parent : Option String
  predicates : List String

private def refName (ref : String) : String :=
  ((ref.splitOn "#").getLast!).replace "\\/" "/"
    |>.replace "\\\\" "\\"
    |>.replace "\\|" "|"

private partial def predicateSets (elem : XmlElem) : List PredicateSet :=
  let here := if elem.tag == "org.eventb.core.poPredicateSet" then
      [{ name := (elem.attr? "name").getD ""
         parent := (elem.attr? "org.eventb.core.parentSet").map refName
         predicates := predicateTexts elem }]
    else []
  here ++ elem.children.flatMap predicateSets

private def chainPredicates (sets : List PredicateSet) : Nat → Option String →
    List String → Option (List String)
  | 0, some _, _ => none
  | _, none, acc => some acc
  | fuel + 1, some name, acc =>
      match sets.find? (fun set => set.name == name) with
      | some set => chainPredicates sets fuel set.parent (set.predicates ++ acc)
      | none => none

private def sequentHypotheses (name : String) (sequent : XmlElem)
    (sets : List PredicateSet) : Option (List String) :=
  let inner := sequent.children.find? (fun child =>
    child.tag == "org.eventb.core.poPredicateSet")
  let parent := inner.bind (fun set =>
    (set.attr? "org.eventb.core.parentSet").map refName)
  let direct := if name.endsWith "/WWD" then predicateTexts sequent else []
  chainPredicates sets (sets.length + 1) parent [] |>.map (· ++ direct)

private def removeEquivalent (target : Formula.Term) : List Formula.Term →
    Option (List Formula.Term)
  | [] => none
  | term :: rest =>
      if Formula.alphaEq (Formula.stripAscriptions target)
          (Formula.stripAscriptions term) then some rest
      else removeEquivalent target rest |>.map (fun remaining => term :: remaining)

private def hypothesisMultisetEqual : List Formula.Term → List Formula.Term → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | term :: rest, other =>
      match removeEquivalent term other with
      | some remaining => hypothesisMultisetEqual rest remaining
      | none => false

private def validateHypotheses (obligation : POG.Obligation) (bpo : XmlElem) :
    Except EventB.Error Unit := do
  let sequent ← match findPoSequent bpo obligation.name with
    | some sequent => pure sequent
    | none => .error (EventB.Error.trust
        s!"Rodin PO artifact has no sequent for `{obligation.name}`")
  let texts ← match sequentHypotheses obligation.name sequent (predicateSets bpo) with
    | some texts => pure texts
    | none => .error (EventB.Error.trust
        s!"Rodin hypothesis chain for `{obligation.name}` is invalid")
  let actual ← match texts.mapM Formula.parse with
    | .ok terms => pure terms
    | .error error => .error (EventB.Error.trust
        s!"Rodin hypothesis for `{obligation.name}` is not a formula: {error.message}")
  unless hypothesisMultisetEqual obligation.hyps actual do
    throw (EventB.Error.trust
      "Rodin hypotheses do not match the canonical obligation context")

private def validateGoal (obligation : POG.Obligation) (bpo : XmlElem) :
    Except EventB.Error Unit := do
  let expected ← match obligation.goal with
    | some goal => pure goal
    | none => .error (EventB.Error.trust
        s!"cannot validate statement-less obligation `{obligation.name}`")
  let sequent ← match findPoSequent bpo obligation.name with
    | some sequent => pure sequent
    | none => .error (EventB.Error.trust
        s!"Rodin PO artifact has no sequent for `{obligation.name}`")
  let source ← match sequentGoal obligation.name sequent with
    | some source => pure source
    | none => .error (EventB.Error.trust
        s!"Rodin sequent `{obligation.name}` has no goal predicate")
  let actual ← match Formula.parse source with
    | .ok term => pure term
    | .error error => .error (EventB.Error.trust
        s!"Rodin goal for `{obligation.name}` is not a formula: {error.message}")
  unless Formula.alphaEq (Formula.stripAscriptions expected)
      (Formula.stripAscriptions actual) do
    throw (EventB.Error.trust
      "Rodin goal does not match the canonical obligation statement")

def validateProvenance (obligation : POG.Obligation) (provenance : Provenance)
    (status : Status) : Except EventB.Error Unit := do
  let (modelName, modelTag) ← rootModel provenance.model
  unless modelName == obligation.component do
    throw (EventB.Error.trust s!
      "Rodin model provenance names `{modelName}`, expected `{obligation.component}`")
  let bpo ← match parseXmlString provenance.bpo with
    | .ok root => pure root
    | .error error => .error (EventB.Error.trust
        s!"invalid PO XML: {error.pretty provenance.bpo.toUTF8}")
  unless bpo.tag == "org.eventb.core.poFile" do
    throw (EventB.Error.trust s!"unsupported Rodin PO root `{bpo.tag}`")
  let expectedSource := if modelTag == "org.eventb.core.machineFile" then
      obligation.component ++ ".bum" else obligation.component ++ ".buc"
  let source ← match bpo.attr? "source" with
    | some value => pure value
    | none => .error (EventB.Error.trust "Rodin PO artifact has no source")
  unless source == expectedSource do
    throw (EventB.Error.trust "Rodin PO source is not the stated model component")
  validateGoal obligation bpo
  validateHypotheses obligation bpo
  let statuses ← importStatuses provenance.statuses
  match status? statuses obligation.name with
  | none => .error (EventB.Error.trust s!
      "proof-status artifact has no status for `{obligation.name}`")
  | some imported =>
      if imported != status then
        .error (EventB.Error.trust s!
          "supplied proof status does not match the parsed artifact for `{obligation.name}`")
      else if !status.discharged then
        .error (EventB.Error.trust s!"proof-status `{status.name}` is not discharged")
      else pure ()

def attachProvenance (ledger : Ledger) (obligation : POG.Obligation)
    (provenance : Provenance) (status : Status) : Except EventB.Error Ledger := do
  validateProvenance obligation provenance status
  attachVerified ledger obligation provenance status.manual

def attach (_ledger : Ledger) (_obligation : POG.Obligation) (_source : String)
    (_status : Status) : Except EventB.Error Ledger :=
  .error (EventB.Error.trust
    "Rodin.attach requires model, PO, and proof-status provenance; use attachProvenance")

private def sampleObligation : POG.Obligation :=
  { component := "Sample", name := "evt/inv/INV", kind := "INV", goal := some (.id "⊤") }

private def sampleSource :=
  "<?xml version=\"1.0\"?><org.eventb.core.psFile><org.eventb.core.psStatus " ++
    "name=\"evt/inv/INV\" " ++
    "org.eventb.core.confidence=\"1000\" org.eventb.core.psManual=\"true\"/>" ++
    "</org.eventb.core.psFile>"

private def sampleProvenance : String → Provenance := fun statuses =>
  { model := "<?xml version=\"1.0\"?><org.eventb.core.machineFile " ++
      "org.eventb.core.name=\"Sample\"/>"
    bpo := "<?xml version=\"1.0\"?>" ++
      "<org.eventb.core.poFile source=\"Sample.bum\"><org.eventb.core.poSequent " ++
      "name=\"evt/inv/INV\"><org.eventb.core.poPredicate " ++
      "org.eventb.core.predicate=\"⊤\"/></org.eventb.core.poSequent></org.eventb.core.poFile>"
    statuses }

#guard match importStatuses sampleSource with
  | .ok [status] => status.name == sampleObligation.name && status.discharged && status.manual
  | _ => false

#guard match importStatuses (sampleSource.replace "name=\"evt/inv/INV\"" "name=\"\"" ) with
  | .error _ => true
  | .ok _ => false

#guard match importStatuses (sampleSource.replace
    "org.eventb.core.confidence=\"1000\"" "org.eventb.core.confidence=\"0\"") with
  | .error _ => true
  | .ok _ => false

#guard match importStatuses (sampleSource.replace
    "</org.eventb.core.psFile>" ("<org.eventb.core.psStatus " ++
      "name=\"evt/inv/INV\" org.eventb.core.confidence=\"1000\" " ++
      "org.eventb.core.psManual=\"true\"/></org.eventb.core.psFile>")) with
  | .error _ => true
  | .ok _ => false

#guard match importStatuses (sampleSource.replace
    "org.eventb.core.psManual=\"true\"" "org.eventb.core.psManual=\"maybe\"") with
  | .error _ => true
  | .ok _ => false

#guard match importStatuses (sampleSource.replace
    " org.eventb.core.psManual=\"true\"" "") with
  | .error _ => true
  | .ok _ => false

#guard match attach (Ledger.ofObligations [sampleObligation])
    sampleObligation sampleSource
      { name := "other/INV", confidence := 1000, manual := false } with
  | .error _ => true
  | .ok _ => false

#guard match attach (Ledger.ofObligations [sampleObligation])
    sampleObligation sampleSource
      { name := sampleObligation.name, confidence := 999, manual := false } with
  | .error _ => true
  | .ok _ => false

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let comparison := compare [sampleObligation] statuses
      comparison.discharged == 1 && comparison.manual == 1 && comparison.missing == 0
  | _ => false

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let other := { sampleObligation with component := "Other" }
      let comparison := compare [sampleObligation, other] statuses
      comparison.scopeAmbiguous && comparison.discharged == 0
  | _ => false

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let duplicate := compare [sampleObligation, sampleObligation] statuses
      duplicate.scopeAmbiguous && duplicate.discharged == 0
  | _ => false

#guard let status : Status := { name := sampleObligation.name, confidence := 1000, manual := true }
  let comparison := compare [sampleObligation] [status, status]
  comparison.scopeAmbiguous && comparison.discharged == 0

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let invalid := { sampleObligation with diagnostics := ["unresolved"] }
      let comparison := compare [invalid] statuses
      comparison.expected == 0 && comparison.discharged == 0
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] => match attachProvenance (Ledger.ofObligations [sampleObligation])
      sampleObligation (sampleProvenance sampleSource) status with
    | .ok ledger =>
        match ledger.entries.head? with
        | some entry =>
            match entry.evidence with
            | .rodinImportedProvenance model bpo statuses digest manual =>
                manual && digest == provenanceDigest { model, bpo, statuses }
            | _ => false
        | none => false
    | .error _ => false
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] =>
      let badModel := { sampleProvenance sampleSource with
        model := (sampleProvenance sampleSource).model.replace
          "org.eventb.core.machineFile" "org.eventb.core.fakeFile" }
      match attachProvenance (Ledger.ofObligations [sampleObligation])
          sampleObligation badModel status with
      | .error _ => true
      | .ok _ => false
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] =>
      let badPo := { sampleProvenance sampleSource with
        bpo := (sampleProvenance sampleSource).bpo.replace
          "org.eventb.core.poFile" "org.eventb.core.fakeFile" }
      match attachProvenance (Ledger.ofObligations [sampleObligation])
          sampleObligation badPo status with
      | .error _ => true
      | .ok _ => false
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] =>
      let badGoal := { sampleProvenance sampleSource with
        bpo := (sampleProvenance sampleSource).bpo.replace "predicate=\"⊤\"" "predicate=\"⊥\"" }
      match attachProvenance (Ledger.ofObligations [sampleObligation])
          sampleObligation badGoal status with
      | .error _ => true
      | .ok _ => false
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] =>
      match attachProvenance (Ledger.ofObligations [sampleObligation]) sampleObligation
          (sampleProvenance sampleSource) status with
      | .ok ledger =>
          match Trust.Ledger.attach ledger sampleObligation
              (.external "stronger" "1" "digest" "checker") with
          | .ok _ => false
          | .error _ => true
      | .error _ => false
  | _ => false

end EventB.Trust.Rodin
