/-
Native Event-B theory authoring. The commands register symbols in the Lean environment,
so later model formulas can use them without quoting or a Rodin workspace.
-/
import EventB.DSL

open EventB

eventb_theory Bounds where
  constant LIMIT : ℤ
  predicate below_limit

eventb_theory Controls where
  imports Bounds
  constant OPEN : BOOL
  predicate active : ℤ → BOOL
  expression clamp : ℤ → ℤ

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
  Theory.Env.mk [Controls, Bounds, Theory.core]

#guard (POG.generateIn theoryEnv theoryProject "TheoryMachine").isEmpty == false
#guard (POG.generateIn theoryEnv theoryProject "TheoryMachine").all
  (fun obligation => !obligation.name.endsWith "/inv2/WD")
#guard match Typing.inferComponentIn theoryEnv theoryProject "TheoryMachine" with
  | .ok (_, errors) => errors.isEmpty
  | .error _ => false
