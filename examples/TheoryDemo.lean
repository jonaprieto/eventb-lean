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
  expression clamp

eventb_context TheoryCtx where
  theories Bounds
  constants cars
  axiom bounded : cars < LIMIT

eventb_machine TheoryMachine where
  sees TheoryCtx
  theories Bounds
  variables cars
  invariant inv1 : cars < LIMIT
  event INITIALISATION where
    action act1 : cars := 0

def theoryProject : Typing.Project :=
  [{ name := "TheoryCtx", elem := TheoryCtx }, { name := "TheoryMachine", elem := TheoryMachine }]

#guard (POG.generate theoryProject "TheoryMachine").isEmpty == false
