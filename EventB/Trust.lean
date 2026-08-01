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

structure Entry where
  obligation : String
  mode : Mode
  evidence : String := ""
  deriving BEq, Repr, Inhabited

structure Ledger where
  entries : List Entry := []
  deriving BEq, Repr, Inhabited

def Ledger.ofObligations (obligations : List POG.Obligation) : Ledger :=
  { entries := obligations.map fun obligation =>
      { obligation := obligation.name, mode := .unproved } }

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

end EventB.Trust
