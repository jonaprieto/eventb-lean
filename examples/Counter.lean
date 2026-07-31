/-
Event-B authored in Lean, not read from a `.bum`.

The same model as Rodin's would be, elaborated to the same `Elem` tree, and fed to the
same obligation generator. That is the point: the DSL is a second front end, not a
second toolchain.
-/
import EventB.DSL

open EventB

eventb_context Ctx where
  sets AIRPLANES
  constants MAX
  axiom axm1 : "MAX ∈ ℕ"

eventb_machine M where
  sees Ctx
  variables sched
  invariant inv1 : "sched ⊆ AIRPLANES"
  event INITIALISATION where
    action act1 : "sched ≔ ∅"
  event Add where
    any a
    guard grd1 : "a ∈ AIRPLANES ∖ sched"
    action act1 : "sched ≔ sched ∪ {a}"

/-- The project this file defines, in the shape the generator wants. -/
def project : Typing.Project := [{ name := "Ctx", elem := Ctx }, { name := "M", elem := M }]

/-! The obligations are derived, not asserted: `Add` must re-establish `inv1` after
assigning `sched`, and initialisation must establish it from `∅`. -/

#guard (POG.generate project "M").map (·.name)
  == ["INITIALISATION/inv1/INV", "Add/inv1/INV"]

#guard ((POG.generate project "M").filterMap (·.goal)).map Formula.print
  == ["({} ⊆ AIRPLANES)", "((sched ∪ {a}) ⊆ AIRPLANES)"]

-- Uncomment to see them printed:
-- #eventb_pog M Ctx
