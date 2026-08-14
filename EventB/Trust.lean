/-
Trust classification for Event-B proof results.

Generating a proposition is not discharging it. This ledger keeps that distinction
explicit so front ends can report what was checked and by whom.
-/

import EventB.POG

namespace EventB.Trust

inductive Mode where
  | kernel
  | smt
  | rodinImported
  | external
  | unproved
  deriving BEq, Repr, Inhabited

def Mode.label : Mode → String
  | .kernel => "kernel-checked"
  | .smt => "smt-trusted"
  | .rodinImported => "rodin-imported"
  | .external => "external-trusted"
  | .unproved => "unproved"

def Mode.rank : Mode → Nat
  | .unproved => 0
  | .external | .rodinImported => 1
  | .smt => 2
  | .kernel => 3

def provenanceFingerprint (model bpo statuses : String) : String :=
  s!"eventb-v2-{String.hash (model ++ "\n" ++ bpo ++ "\n" ++ statuses)}"

inductive Evidence where
  | none
  | kernel (declaration : String) (axioms : List String := [])
  | smt (solver : String) (version : String) (inputDigest : String) (verifier : String)
  | external (tool : String) (version : String) (artifactDigest : String) (verifier : String)
  | rodinImported (source : String) (digest : String) (manual : Bool)
  | rodinImportedProvenance (model : String) (bpo : String) (statuses : String)
      (digest : String) (manual : Bool)
  deriving BEq, Repr, Inhabited

def Evidence.mode : Evidence → Mode
  | .none => .unproved
  | .kernel _ _ => .kernel
  | .smt _ _ _ _ => .smt
  | .external _ _ _ _ => .external
  | .rodinImported _ _ _ => .rodinImported
  | .rodinImportedProvenance _ _ _ _ _ => .rodinImported

def Evidence.isWellFormed : Evidence → Bool
  | .none => false
  | .kernel declaration _ => !declaration.isEmpty
  | .smt solver version digest verifier =>
      !solver.isEmpty && !version.isEmpty && !digest.isEmpty && !verifier.isEmpty
  | .external tool version digest verifier =>
      !tool.isEmpty && !version.isEmpty && !digest.isEmpty && !verifier.isEmpty
  -- Legacy status-only evidence remains a display-compatible constructor, but it is
  -- never accepted as ledger evidence without model/BPO provenance.
  | .rodinImported _ _ _ => false
  | .rodinImportedProvenance model bpo statuses digest _ =>
      !model.isEmpty && !bpo.isEmpty && !statuses.isEmpty &&
        digest == provenanceFingerprint model bpo statuses

def fingerprint (canonical : String) : String :=
  s!"eventb-v1-{String.hash canonical}"

structure Entry where
  component : String := ""
  obligation : String
  fingerprint : String
  /-- Exact canonical source retained so local attachment does not rely on hash equality. -/
  canonical : String := ""
  /-- Semantic context fingerprint required for kernel entries. -/
  semanticFingerprint : String := ""
  mode : Mode
  evidence : Evidence := .none
  deriving BEq, Repr, Inhabited

def Entry.isConsistent (entry : Entry) : Bool :=
    !entry.component.isEmpty && !entry.obligation.isEmpty &&
    !entry.canonical.isEmpty && entry.fingerprint == Trust.fingerprint entry.canonical &&
    (entry.mode != .kernel || !entry.semanticFingerprint.isEmpty) &&
    entry.mode == entry.evidence.mode &&
    (entry.mode == .unproved || entry.evidence.isWellFormed)

structure Ledger where
  entries : List Entry := []
  deriving BEq, Repr, Inhabited

def Ledger.ofObligations (obligations : List POG.Obligation) : Ledger :=
  { entries := obligations.map fun obligation =>
      { component := obligation.component, obligation := obligation.name
        fingerprint := fingerprint obligation.canonical, canonical := obligation.canonical,
        mode := .unproved } }

private def sameEntry (entry : Entry) (component name : String) : Bool :=
  entry.component == component && entry.obligation == name

def Ledger.entry? (ledger : Ledger) (component name : String) : Option Entry :=
  ledger.entries.find? (sameEntry · component name)

def Ledger.validate (ledger : Ledger) : Except EventB.Error Unit :=
  let rec go (seen : List String) : List Entry → Except EventB.Error Unit
    | [] => .ok ()
    | entry :: rest =>
        let key := entry.component ++ "\t" ++ entry.obligation
        if seen.contains key then
          .error (EventB.Error.trust s!"ledger has duplicate entry `{key}`")
        else if entry.mode == .kernel then
          .error (EventB.Error.trust
            s!"kernel entry `{key}` requires Trust.Replay validation")
        else if !entry.isConsistent then
          .error (EventB.Error.trust s!"ledger entry `{key}` is inconsistent")
        else go (key :: seen) rest
  go [] ledger.entries

def Ledger.attach (ledger : Ledger) (obligation : POG.Obligation) (evidence : Evidence) :
    Except EventB.Error Ledger :=
  let expected := fingerprint obligation.canonical
  if let .error error := ledger.validate then
    .error error
  else if !obligation.diagnostics.isEmpty then
    .error (EventB.Error.trust
      s!"cannot attach evidence to `{obligation.component}:{obligation.name}` with diagnostics")
  else if obligation.goal.isNone then
    .error (EventB.Error.trust
      s!"cannot attach evidence to statement-less obligation `{obligation.name}`")
  else if evidence matches .kernel .. then
    .error (EventB.Error.trust
      "kernel evidence must be validated by Trust.Replay before ledger attachment")
  else if evidence matches .rodinImported .. || evidence matches .rodinImportedProvenance .. then
    .error (EventB.Error.trust
      "Rodin evidence must be attached through Trust.Rodin after artifact parsing")
  else if !evidence.isWellFormed then
    .error (EventB.Error.trust "evidence metadata is incomplete")
  else if ledger.entry? obligation.component obligation.name |>.isNone then
    .error (EventB.Error.trust
      s!"obligation `{obligation.component}:{obligation.name}` is not in the ledger")
  else if ledger.entries.countP (sameEntry · obligation.component obligation.name) != 1 then
    .error (EventB.Error.trust
      s!"ledger has duplicate entries for `{obligation.component}:{obligation.name}`")
  else if (ledger.entry? obligation.component obligation.name |>.get!).canonical !=
      obligation.canonical then
    .error (EventB.Error.trust
      s!"evidence canonical mismatch for `{obligation.component}:{obligation.name}`")
  else if (ledger.entry? obligation.component obligation.name |>.get!).fingerprint != expected then
    .error (EventB.Error.trust
      s!"evidence fingerprint mismatch for `{obligation.component}:{obligation.name}`")
  else
    let entry := ledger.entry? obligation.component obligation.name |>.get!
    if !entry.isConsistent then
      .error (EventB.Error.trust
        s!"ledger entry for `{obligation.component}:{obligation.name}` is internally inconsistent")
    else if entry.mode != .unproved && Mode.rank evidence.mode <= Mode.rank entry.mode then
      .error (EventB.Error.trust
        (s!"evidence for `{obligation.component}:{obligation.name}` cannot be replaced " ++
          "by equal or weaker evidence"))
    else
      .ok { entries := ledger.entries.map fun current =>
        if sameEntry current obligation.component obligation.name then
          { current with mode := evidence.mode, evidence := evidence }
        else current }

def Ledger.count (ledger : Ledger) (mode : Mode) : Nat :=
  ledger.entries.countP (·.mode == mode)

def Ledger.total (ledger : Ledger) : Nat :=
  ledger.entries.length

def Ledger.summary (ledger : Ledger) : String :=
  let modes := [Mode.kernel, .smt, .rodinImported, .external, .unproved]
  modes.foldl (fun result mode =>
    let count := ledger.count mode
    if count == 0 then result
    else if result.isEmpty then s!"{mode.label}: {count}"
    else result ++ s!", {mode.label}: {count}") ""

#guard Mode.kernel.label == "kernel-checked"
#guard (Ledger.ofObligations []).total == 0
#guard fingerprint "same" == fingerprint "same"
#guard fingerprint "same" != fingerprint "changed"
#guard !Evidence.isWellFormed
  (.rodinImportedProvenance "model" "bpo" "status" "forged" false)

private def sampleObligation : POG.Obligation :=
  { component := "Sample", name := "INITIALISATION/inv1/INV", kind := "INV"
    goal := some (.id "⊤") }

private def sampleLedger : Ledger := Ledger.ofObligations [sampleObligation]

private def inconsistentLedger : Ledger :=
  { entries := [{ sampleLedger.entries.head! with evidence := .kernel "forged" }] }

private def unrelatedObligation : POG.Obligation :=
  { sampleObligation with name := "INITIALISATION/inv2/INV" }

private def unrelatedInconsistentLedger : Ledger :=
  { entries := [inconsistentLedger.entries.head!,
      (Ledger.ofObligations [unrelatedObligation]).entries.head!] }

private def forgedKernelLedger : Ledger :=
  { entries := [{ sampleLedger.entries.head! with
      mode := .kernel, evidence := .kernel "forged" }] }

private def legacyRodinLedger : Ledger :=
  { entries := [{ sampleLedger.entries.head! with
      mode := .rodinImported, evidence := .rodinImported "status.bps" "digest" false }] }

private def renamedSample : POG.Obligation :=
  { sampleObligation with name := "display-only", kind := "INV" }

#guard sampleObligation.canonical != renamedSample.canonical
#guard sampleObligation.canonical !=
  { sampleObligation with goal := some (.id "⊥") }.canonical
#guard ({ sampleObligation with diagnostics := ["a\nb"] }).canonical !=
  ({ sampleObligation with diagnostics := ["a", "b"] }).canonical

#guard match sampleLedger.attach sampleObligation
    (.external "sample" "1" "digest" "checker") with
  | .ok ledger => ledger.count .external == 1
  | .error _ => false

#guard match sampleLedger.attach sampleObligation
    (.external "sample" "1" "digest" "checker") with
  | .ok ledger => match ledger.attach sampleObligation
      (.external "other" "1" "digest" "checker") with
    | .error _ => true
    | .ok _ => false
  | .error _ => false
#guard match sampleLedger.attach sampleObligation (.kernel "No.Such.Declaration") with
  | .error _ => true
  | .ok _ => false
#guard match Ledger.attach
    inconsistentLedger
    sampleObligation (.external "sample" "1" "digest" "checker") with
  | .error _ => true
  | .ok _ => false
#guard match Ledger.attach
    unrelatedInconsistentLedger
    unrelatedObligation (.external "sample" "1" "digest" "checker") with
  | .error _ => true
  | .ok _ => false
#guard match forgedKernelLedger.validate with
  | .error _ => true
  | .ok _ => false
#guard match legacyRodinLedger.validate with
  | .error _ => true
  | .ok _ => false
#guard match sampleLedger.attach
    { sampleObligation with goal := some (.id "⊥") } (.kernel "Sample.inv1") with
  | .error _ => true
  | .ok _ => false
#guard match sampleLedger.attach sampleObligation (.kernel "") with
  | .error _ => true
  | .ok _ => false
#guard match sampleLedger.attach sampleObligation
    (.rodinImported "status.bps" "digest" false) with
  | .error _ => true
  | .ok _ => false

end EventB.Trust
