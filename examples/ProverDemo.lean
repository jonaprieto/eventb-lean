/- A checked inventory of the deliberately small local discharge baseline. -/
import EventB.Prover.Local

open EventB EventB.POG EventB.Prover.Local

private def obligations : List Obligation :=
  [{ component := "Demo", name := "true", kind := "THM", goal := some (.id "⊤") },
   { component := "Demo", name := "refl", kind := "THM",
     goal := some (.bin "=" (.id "x") (.id "x")) },
   { component := "Demo", name := "open", kind := "INV", goal := some (.id "x") }]

def baseline : List Result := obligations.map prove

#guard baseline.countP Result.discharged == 2
#guard baseline.countP (fun result => result.evidence.mode == .external) == 2
