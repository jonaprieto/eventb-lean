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

structure Comparison where
  expected : Nat
  discharged : Nat
  automatic : Nat
  manual : Nat
  missing : Nat
  stale : Nat
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
  let confidenceSource ← attr elem "org.eventb.core.confidence"
  let confidence ← match natValue confidenceSource with
    | some value => pure value
    | none => .error s!"invalid confidence `{confidenceSource}`"
  let manual ← match elem.attr? "org.eventb.core.psManual" with
    | some "true" => pure true
    | some "false" => pure false
    | some value => .error s!"invalid psManual `{value}`"
    | none => pure false
  pure { name, confidence, manual }

def importStatuses (source : String) : Except String (List Status) := do
  let root ← match parseXmlString source with
    | .ok root => pure root
    | .error error => .error s!"invalid Rodin proof-status XML: {error.pretty source.toUTF8}"
  unless root.tag == "org.eventb.core.psFile" do
    throw s!"root is not a proof-status file: `{root.tag}`"
  root.children.mapM parseStatus

private def status? (statuses : List Status) (name : String) : Option Status :=
  statuses.find? (·.name == name)

def compare (obligations : List POG.Obligation) (statuses : List Status) : Comparison :=
  let expected := obligations.map (·.name)
  let present := obligations.filterMap fun obligation =>
    match status? statuses obligation.name with
    | some status => if status.discharged then some (obligation.name, status) else none
    | none => none
  { expected := obligations.length
    discharged := present.length
    automatic := present.countP (·.2.manual == false)
    manual := present.countP (·.2.manual)
    missing := obligations.countP (status? statuses ·.name |>.isNone)
    stale := statuses.countP (fun status => !expected.contains status.name) }

def attach (ledger : Ledger) (obligation : POG.Obligation) (source : String)
    (status : Status) : Except String Ledger :=
  if status.discharged then
    let evidence := .rodinImported source (s!"eventb-v1-{String.hash source}") status.manual
    ledger.attach obligation evidence
  else
    pure ledger

private def sampleObligation : POG.Obligation :=
  { component := "Sample", name := "evt/inv/INV", kind := "INV", goal := some (.id "⊤") }

private def sampleSource :=
  "<?xml version=\"1.0\"?><org.eventb.core.psFile><org.eventb.core.psStatus " ++
    "name=\"evt/inv/INV\" " ++
    "org.eventb.core.confidence=\"1000\" org.eventb.core.psManual=\"true\"/>" ++
    "</org.eventb.core.psFile>"

#guard match importStatuses sampleSource with
  | .ok [status] => status.name == sampleObligation.name && status.discharged && status.manual
  | _ => false

#guard match importStatuses sampleSource with
  | .ok statuses =>
      let comparison := compare [sampleObligation] statuses
      comparison.discharged == 1 && comparison.manual == 1 && comparison.missing == 0
  | _ => false

#guard match importStatuses sampleSource with
  | .ok [status] => match attach (Ledger.ofObligations [sampleObligation])
      sampleObligation "sample.bps" status with
    | .ok ledger => ledger.count .rodinImported == 1
    | .error _ => false
  | _ => false

end EventB.Trust.Rodin
