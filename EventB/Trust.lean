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

inductive Evidence where
  | none
  | kernel (declaration : String) (axioms : List String := [])
  | smt (solver : String) (version : String) (inputDigest : String) (verifier : String)
  | external (tool : String) (version : String) (artifactDigest : String) (verifier : String)
  | rodinImported (source : String) (digest : String) (manual : Bool)
  deriving BEq, Repr, Inhabited

def Evidence.mode : Evidence → Mode
  | .none => .unproved
  | .kernel _ _ => .kernel
  | .smt _ _ _ _ => .smt
  | .external _ _ _ _ => .external
  | .rodinImported _ _ _ => .rodinImported

def Evidence.isWellFormed : Evidence → Bool
  | .none => false
  | .kernel declaration _ => !declaration.isEmpty
  | .smt solver version digest verifier =>
      !solver.isEmpty && !version.isEmpty && !digest.isEmpty && !verifier.isEmpty
  | .external tool version digest verifier =>
      !tool.isEmpty && !version.isEmpty && !digest.isEmpty && !verifier.isEmpty
  | .rodinImported source digest _ => !source.isEmpty && !digest.isEmpty

def fingerprint (canonical : String) : String :=
  s!"eventb-v1-{String.hash canonical}"

structure Entry where
  component : String := ""
  obligation : String
  fingerprint : String
  mode : Mode
  evidence : Evidence := .none
  deriving BEq, Repr, Inhabited

structure Ledger where
  entries : List Entry := []
  deriving BEq, Repr, Inhabited

def Ledger.ofObligations (obligations : List POG.Obligation) : Ledger :=
  { entries := obligations.map fun obligation =>
      { component := obligation.component, obligation := obligation.name
        fingerprint := fingerprint obligation.canonical, mode := .unproved } }

private def key (component name : String) : String := component ++ "\n" ++ name

def Ledger.entry? (ledger : Ledger) (component name : String) : Option Entry :=
  ledger.entries.find? (fun entry => key entry.component entry.obligation == key component name)

def Ledger.attach (ledger : Ledger) (obligation : POG.Obligation) (evidence : Evidence) :
    Except String Ledger :=
  let expected := fingerprint obligation.canonical
  if !evidence.isWellFormed then .error "evidence metadata is incomplete"
  else if ledger.entry? obligation.component obligation.name |>.isNone then
    .error s!"obligation `{obligation.component}:{obligation.name}` is not in the ledger"
  else if (ledger.entry? obligation.component obligation.name |>.get!).fingerprint != expected then
    .error s!"evidence fingerprint mismatch for `{obligation.component}:{obligation.name}`"
  else
    .ok { entries := ledger.entries.map fun entry =>
      if key entry.component entry.obligation == key obligation.component obligation.name then
        { entry with mode := evidence.mode, evidence := evidence }
      else entry }

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

private def sampleObligation : POG.Obligation :=
  { component := "Sample", name := "INITIALISATION/inv1/INV", kind := "INV"
    goal := some (.id "⊤") }

private def sampleLedger : Ledger := Ledger.ofObligations [sampleObligation]

private def renamedSample : POG.Obligation :=
  { sampleObligation with name := "display-only", kind := "INV" }

#guard sampleObligation.canonical == renamedSample.canonical
#guard sampleObligation.canonical !=
  { sampleObligation with goal := some (.id "⊥") }.canonical

#guard match sampleLedger.attach sampleObligation (.kernel "Sample.inv1") with
  | .ok ledger => ledger.count .kernel == 1
  | .error _ => false
#guard match sampleLedger.attach
    { sampleObligation with goal := some (.id "⊥") } (.kernel "Sample.inv1") with
  | .error _ => true
  | .ok _ => false
#guard match sampleLedger.attach sampleObligation (.kernel "") with
  | .error _ => true
  | .ok _ => false

end EventB.Trust
