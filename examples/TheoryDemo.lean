/-
Native Event-B theory authoring. The commands register symbols in the Lean environment,
so later model formulas can use them without quoting or a Rodin workspace.
-/
import Widgets

open EventB

eventb_theory Bounds where
  constant LIMIT : ℤ
  predicate below_limit

eventb_theory Controls where
  imports Bounds
  constant OPEN : BOOL
  predicate active : ℤ → BOOL
  expression clamp : ℤ → ℤ

eventb_theory Algebra where
  datatype Colour where red blue
  definition zero : ℤ where 0
  rewrite add_zero where "x + 0" => "x"
  inference lt_identity where "x < y" => "x < y"
  theorem zero_eq where "0 = 0"

eventb_context TheoryCtx where
  uses Controls
  constants cars
  axiom bounded : cars < LIMIT
  axiom open_value : OPEN = TRUE

eventb_machine TheoryMachine where
  sees TheoryCtx
  uses Controls
  variables cars
  invariant inv1 : cars < LIMIT
  invariant inv2 : clamp (cars) < LIMIT
  invariant inv3 : active (cars)
  event INITIALISATION where
    action act1 : cars := 0

def theoryProject : Typing.Project :=
  [ { name := "TheoryCtx", elem := TheoryCtx, theories := ["Controls"] }
  , { name := "TheoryMachine", elem := TheoryMachine, theories := ["Controls"] } ]

def theoryEnv : Theory.Env :=
  match Theory.register [Bounds, Controls, Algebra] with
  | .ok env => env
  | .error _ => Theory.empty

#guard (Theory.declaration? theoryEnv ["Algebra"] "Colour").isSome
#guard (Theory.declaration? theoryEnv ["Algebra"] "add_zero").isSome

#guard (POG.generateIn theoryEnv theoryProject "TheoryMachine").isEmpty == false
#guard (POG.generateIn theoryEnv theoryProject "TheoryMachine").all
  (fun obligation => !obligation.name.endsWith "/inv2/WD")
#guard match Typing.inferComponentIn theoryEnv theoryProject "TheoryMachine" with
  | .ok (_, errors) => errors.isEmpty
  | .error _ => false

#eventb_pog_in theoryEnv TheoryMachine TheoryCtx
#eventb_pog_widget_in theoryEnv theoryProject TheoryMachine
