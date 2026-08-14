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

def compare (obligations : List POG.Obligation) (statuses : List Status) : Comparison :=
  let eligible := obligations.filter fun obligation =>
    obligation.diagnostics.isEmpty && obligation.goal.isSome
  let expected := eligible.map (·.name)
  let duplicateExpected := duplicateKeys [] (eligible.map fun obligation =>
    obligation.component ++ "\t" ++ obligation.name)
  let scopeAmbiguous := (eligible.map (·.component)).eraseDups.length > 1 ||
    !duplicateExpected.isEmpty
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
    (source : String) (manual : Bool) : Except EventB.Error Ledger :=
  let evidence := .rodinImported source (s!"eventb-v1-{String.hash source}") manual
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

private partial def hasPoSequent : XmlElem → String → Bool
  | elem, name =>
      (elem.tag == "org.eventb.core.poSequent" && elem.attr? "name" == some name) ||
        elem.children.any (fun child => hasPoSequent child name)

private def rootModelName (source : String) : Except EventB.Error String := do
  let root ← match parseXmlString source with
    | .ok root => pure root
    | .error error => .error (EventB.Error.trust
        s!"invalid model XML: {error.pretty source.toUTF8}")
  match root.attr? "org.eventb.core.name" with
  | some name => pure name
  | none => .error (EventB.Error.trust "model XML has no component name")

def attachProvenance (ledger : Ledger) (obligation : POG.Obligation)
    (provenance : Provenance) (status : Status) : Except EventB.Error Ledger := do
  let modelName ← rootModelName provenance.model
  unless modelName == obligation.component do
    throw (EventB.Error.trust s!
      "Rodin model provenance names `{modelName}`, expected `{obligation.component}`")
  let bpo ← match parseXmlString provenance.bpo with
    | .ok root => pure root
    | .error error => .error (EventB.Error.trust
        s!"invalid PO XML: {error.pretty provenance.bpo.toUTF8}")
  unless hasPoSequent bpo obligation.name do
    throw (EventB.Error.trust s!
      "Rodin PO artifact has no sequent for `{obligation.name}`")
  unless (provenance.bpo.splitOn (obligation.component ++ ".bum")).length > 1 do
    throw (EventB.Error.trust
      "Rodin PO artifact is not bound to the stated model component")
  let statuses ← importStatuses provenance.statuses
  match status? statuses obligation.name with
  | none => .error (EventB.Error.trust s!
      "proof-status artifact has no status for `{obligation.name}`")
  | some imported =>
      if imported != status then
        .error (EventB.Error.trust s!
          "supplied proof status does not match the parsed artifact for `{obligation.name}`")
      else if status.confidence == 0 then
        .error (EventB.Error.trust s!"proof-status `{status.name}` has zero confidence")
      else if status.discharged then
        attachVerified ledger obligation provenance.statuses status.manual
      else
        .error (EventB.Error.trust s!"proof-status `{status.name}` is not discharged")

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
      "name=\"evt/inv/INV\"/></org.eventb.core.poFile>"
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

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let invalid := { sampleObligation with diagnostics := ["unresolved"] }
      let comparison := compare [invalid] statuses
      comparison.expected == 0 && comparison.discharged == 0
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] => match attachProvenance (Ledger.ofObligations [sampleObligation])
      sampleObligation (sampleProvenance sampleSource) status with
    | .ok ledger => ledger.count .rodinImported == 1
    | .error _ => false
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
