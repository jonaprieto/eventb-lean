/-
  Bounded, model-derived NAT/VAR fixture.

  This file is intentionally disjoint from the production POG and adapter modules.
  It checks the exact generated terms, the exact source variant, the convergence
  mode, and forged-goal rejection.  The small finite model below supplies a
  kernel-checked semantic sanity check for the same decrementing event.
-/

import EventB.POG

namespace EventB.VariantFixtures

open EventB EventB.Formula EventB.POG EventB.Typing

private def childrenOf (element : Elem) (tag : String) : List Elem :=
  element.children.filter (fun child => child.tag == "org.eventb.core." ++ tag)

private def attrOf (element : Elem) (key : String) : Option String :=
  element.attr? ("org.eventb.core." ++ key)

private def componentElements (project : Project) (component : String) :
    Option Elem :=
  (lookupComponent project component).map (·.elem)

private def variantExpressions (project : Project) (component : String) :
    List (Option Term) :=
  (componentElements project component).toList.flatMap fun element =>
    (childrenOf element "variant").map fun variant =>
      (attrOf variant "expression").bind (Formula.parse · |>.toOption)

/- A fixture-local uniqueness check: the checked production source is accepted only
   when this project has exactly one variant, so a second variant cannot silently be
   ignored by a first-match lookup. -/
private def uniqueVariantExpression? (project : Project) (component : String) :
    Option Term :=
  match (variantExpressions project component).filterMap id with
  | [expression] => some expression
  | _ => none

private def eventConvergence? (project : Project) (component event : String) :
    Option String :=
  (componentElements project component).bind fun element =>
    (childrenOf element "event").find? (fun candidate =>
      attrOf candidate "label" == some event) |>.bind (attrOf · "convergence")

private def parsed? (source : String) : Option Term :=
  (Formula.parse source).toOption

def boundedNatVariantProject : Project :=
  [{ name := "M"
     elem := .machineFile [ ("org.eventb.core.name", "M") ]
       [ .variable [ ("org.eventb.core.identifier", "x") ] []
       , .invariant [ ("org.eventb.core.label", "type")
                    , ("org.eventb.core.predicate", "x ∈ ℤ") ] []
       , .variant [ ("org.eventb.core.expression", "x") ] []
       , .event [ ("org.eventb.core.label", "INITIALISATION") ]
           [ .action [ ("org.eventb.core.label", "set")
                     , ("org.eventb.core.assignment", "x ≔ 2") ] [] ]
       , .event [ ("org.eventb.core.label", "step")
                , ("org.eventb.core.convergence", "1") ]
           [ .guard [ ("org.eventb.core.label", "positive")
                    , ("org.eventb.core.predicate", "x > 0") ] []
           , .action [ ("org.eventb.core.label", "decrement")
                     , ("org.eventb.core.assignment", "x ≔ x − 1") ] [] ]
       , .event [ ("org.eventb.core.label", "hold")
                , ("org.eventb.core.convergence", "2") ]
           [ .action [ ("org.eventb.core.label", "unchanged")
                     , ("org.eventb.core.assignment", "x ≔ x") ] [] ] ] }]

private def variantGoal? (project : Project) (event kind : String)
    (goal : Option Term) : Bool :=
  match generateCheckedIn Theory.empty project "M" with
  | .error _ => false
  | .ok obligations =>
      obligations.any fun obligation =>
          obligation.component == "M" && obligation.name == event ++ "/" ++ kind &&
          obligation.kind == kind && obligation.goal == goal &&
          generatedSourceBound project obligation

private def exactVariantGoal? (project : Project) (event kind mode : String)
    (goal : Option Term) : Bool :=
  uniqueVariantExpression? project "M" == some (.id "x") &&
    eventConvergence? project "M" event == some mode &&
    variantGoal? project event kind goal

private def exactVariantSource? : Option Term :=
  uniqueVariantExpression? boundedNatVariantProject "M"

private def assignmentUpdates? (project : Project) (component event : String) :
    Option (List (String × Term)) :=
  (componentElements project component).bind fun element =>
    (childrenOf element "event").find? (fun candidate =>
      attrOf candidate "label" == some event) |>.bind fun currentEvent =>
      (childrenOf currentEvent "action").mapM fun action => do
        let source ← attrOf action "assignment"
        let term ← (Formula.parse source).toOption
        match term with
        | .bin "≔" (.id name) rhs => some (name, rhs)
        | _ => none

private def exactStepSource? : Option (List (String × Term)) :=
  assignmentUpdates? boundedNatVariantProject "M" "step"

/- Exact provenance and exact generated goals.  The parser comparison is AST equality,
   not a printed-name or obligation-count check. -/
#guard exactVariantSource? == some (.id "x")
#guard eventConvergence? boundedNatVariantProject "M" "step" == some "1"
#guard eventConvergence? boundedNatVariantProject "M" "hold" == some "2"
#guard exactStepSource? == some [("x", .bin "−" (.id "x") (.num 1))]

#guard exactVariantGoal? boundedNatVariantProject "step" "NAT" "1"
  (parsed? "x ∈ ℕ")
#guard exactVariantGoal? boundedNatVariantProject "step" "VAR" "1"
  (parsed? "x − 1 < x")
#guard exactVariantGoal? boundedNatVariantProject "hold" "NAT" "2"
  (parsed? "x ∈ ℕ")
#guard exactVariantGoal? boundedNatVariantProject "hold" "VAR" "2"
  (parsed? "x ≤ x")

/- Forged formula, wrong event, and wrong convergence controls. -/
#guard !exactVariantGoal? boundedNatVariantProject "step" "VAR" "1"
  (parsed? "x ≤ x")
#guard !exactVariantGoal? boundedNatVariantProject "step" "VAR" "2"
  (parsed? "x − 1 < x")
#guard !exactVariantGoal? boundedNatVariantProject "hold" "VAR" "1"
  (parsed? "x ≤ x")
#guard !variantGoal? boundedNatVariantProject "missing" "VAR" (parsed? "x < x")

private def alteredVariantProject : Project :=
  [{ name := "M"
     elem := .machineFile [ ("org.eventb.core.name", "M") ]
       [ .variable [ ("org.eventb.core.identifier", "x") ] []
       , .invariant [ ("org.eventb.core.label", "type")
                    , ("org.eventb.core.predicate", "x ∈ ℤ") ] []
       , .variant [ ("org.eventb.core.expression", "x + 1") ] []
       , .event [ ("org.eventb.core.label", "INITIALISATION") ] []
       , .event [ ("org.eventb.core.label", "step")
                , ("org.eventb.core.convergence", "1") ]
           [ .action [ ("org.eventb.core.label", "decrement")
                     , ("org.eventb.core.assignment", "x ≔ x − 1") ] [] ] ] }]

private def duplicateVariantProject : Project :=
  [{ name := "M"
     elem := .machineFile [ ("org.eventb.core.name", "M") ]
       [ .variable [ ("org.eventb.core.identifier", "x") ] []
       , .variant [ ("org.eventb.core.expression", "x") ] []
       , .variant [ ("org.eventb.core.expression", "x + 1") ] [] ] }]

#guard !variantGoal? alteredVariantProject "step" "NAT" (parsed? "x ∈ ℕ")
#guard variantGoal? alteredVariantProject "step" "NAT" (parsed? "x + 1 ∈ ℕ")
#guard !exactVariantGoal? alteredVariantProject "step" "NAT" "1"
  (parsed? "x + 1 ∈ ℕ")
#guard uniqueVariantExpression? duplicateVariantProject "M" |>.isNone

/- A finite semantic model for the exact decrementing source action. -/
inductive BoundedState where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

def measure : BoundedState → Nat
  | .zero => 0
  | .one => 1
  | .two => 2

def sourceValue : BoundedState → Int
  | .zero => 0
  | .one => 1
  | .two => 2

def decrement : BoundedState → BoundedState → Prop
  | .one, .zero => True
  | .two, .one => True
  | _, _ => False

def boundedStates : List BoundedState := [.zero, .one, .two]

def boundedTransitions : List (BoundedState × BoundedState) :=
  [(.one, .zero), (.two, .one)]

theorem bounded_nat : ∀ state, 0 ≤ measure state := by
  intro state
  cases state <;> decide

theorem bounded_var : ∀ before after,
    decrement before after → measure after < measure before := by
  intro before after step
  cases before <;> cases after <;> simp [decrement, measure] at step ⊢

theorem bounded_source_action : ∀ before after,
    decrement before after → sourceValue after = sourceValue before - 1 := by
  intro before after step
  cases before <;> cases after <;> simp [decrement, sourceValue] at step ⊢

theorem no_unit_source_cover :
    ¬ ∃ encode : Unit → BoundedState × BoundedState,
      ∀ transition ∈ boundedTransitions,
        ∃ state, encode state = transition := by
  rintro ⟨encode, complete⟩
  obtain ⟨zeroState, zeroEncoded⟩ := complete (.one, .zero) (by simp [boundedTransitions])
  obtain ⟨oneState, oneEncoded⟩ := complete (.two, .one) (by simp [boundedTransitions])
  have sameState : zeroState = oneState := Subsingleton.elim _ _
  have equalTransitions : (BoundedState.one, BoundedState.zero) =
      (BoundedState.two, BoundedState.one) := by
    calc
      (BoundedState.one, BoundedState.zero) = encode zeroState := zeroEncoded.symm
      _ = encode oneState := congrArg encode sameState
      _ = (BoundedState.two, BoundedState.one) := oneEncoded
  cases equalTransitions

#guard boundedStates.all (fun state => 0 ≤ measure state)
#guard boundedTransitions.all (fun transition =>
  measure transition.2 < measure transition.1)
#guard boundedTransitions.all (fun transition =>
  sourceValue transition.2 == sourceValue transition.1 - 1)

end EventB.VariantFixtures
