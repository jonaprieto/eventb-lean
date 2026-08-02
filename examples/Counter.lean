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
  variables sched count rel
  invariant inv1 : "sched ⊆ AIRPLANES"
  invariant inv2 : "count ∈ ℕ"
  invariant inv3 : "rel ∈ AIRPLANES ↔ AIRPLANES"
  event INITIALISATION where
    action act1 : "sched ≔ ∅"
    action act2 : "count ≔ 0"
    action act3 : "rel ≔ ∅"
  event Add where
    any a
    guard grd1 : "a ∈ AIRPLANES ∖ sched"
    action act1 : "sched ≔ sched ∪ {a}"
  event Count where
    any a
    guard grd1 : "a ∈ AIRPLANES"
    action act1 : "count ≔ card({a})"
  event Relabel where
    any a
    guard grd1 : "a ∈ AIRPLANES"
    action act1 : "rel(a) ≔ a"

/-- The project this file defines, in the shape the generator wants. -/
def project : Typing.Project := [{ name := "Ctx", elem := Ctx }, { name := "M", elem := M }]

/-! The obligations are derived, not asserted: `Add` must re-establish `inv1` after
assigning `sched`, and initialisation must establish it from `∅`. -/

#guard (POG.generate project "M").map (·.name)
  |>.contains "INITIALISATION/inv1/INV"
#guard (POG.generate project "M").map (·.name) |>.contains "Add/inv1/INV"

#guard ((POG.generate project "M").filterMap (·.goal)).map Formula.print
  |>.contains "({} ⊆ AIRPLANES)"
#guard ((POG.generate project "M").filterMap (·.goal)).map Formula.print
  |>.contains "((sched ∪ {a}) ⊆ AIRPLANES)"

#guard (POG.generate project "M").map (·.name) |>.contains "Count/act1/WD"
#guard !((POG.generate project "M").map (·.name) |>.contains "Relabel/act1/WD")

-- Uncomment to see them printed:
-- #eventb_pog M Ctx
