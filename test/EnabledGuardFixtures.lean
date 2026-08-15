/- Focused positive and negative semantic enabled-event source fixture. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def enabledEventProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "step")]
          [.guard [("org.eventb.core.label", "enabled"),
                   ("org.eventb.core.predicate", "x = 0")] []
           , .action [("org.eventb.core.label", "stutter"),
                      ("org.eventb.core.assignment", "x ≔ x")] []]] }]

#guard match generateCheckedIn EventB.Theory.empty enabledEventProject "M" with
  | .ok _ => true
  | .error _ => false

private def enabledEventSource :
    CheckedEventSource EventB.Theory.empty enabledEventProject "M" "step" :=
  (CheckedEventSource.fromProject EventB.Theory.empty enabledEventProject "M" "step").get
    (by native_decide)

private def enabledGuardSource :
    CheckedGuardSource EventB.Theory.empty enabledEventProject "M" "step" :=
  (CheckedGuardSource.fromProject EventB.Theory.empty enabledEventProject "M" "step").get
    (by native_decide)

#guard enabledEventSource.declarations == [("x", .int)]
#guard enabledEventSource.updates == [("x", .id "x")]
#guard enabledGuardSource.predicates ==
  [.bin "=" (.id "x") (.num 0)]

private def enabledTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 0)] }
    after := { values := [("x", .integer 0)] }
    declarations := [("x", .int)] }

private def disabledTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 1)] }
    after := { values := [("x", .integer 1)] }
    declarations := [("x", .int)] }

private theorem enabledAction :
    enabledEventSource.assignmentAction 128 enabledTransition := by
  have declarations : enabledEventSource.declarations = [("x", .int)] := by
    native_decide
  have updates : enabledEventSource.updates = [("x", .id "x")] := by
    native_decide
  change assignmentRelation 128 enabledEventSource.declarations
    enabledTransition enabledEventSource.updates
  rw [declarations, updates]
  exact assignmentRelation_x_self_zero

private theorem disabledAction :
    enabledEventSource.assignmentAction 128 disabledTransition := by
  have declarations : enabledEventSource.declarations = [("x", .int)] := by
    native_decide
  have updates : enabledEventSource.updates = [("x", .id "x")] := by
    native_decide
  change assignmentRelation 128 enabledEventSource.declarations
    disabledTransition enabledEventSource.updates
  rw [declarations, updates]
  unfold assignmentRelation
  native_decide

private theorem enabledGuard :
    enabledGuardSource.holds 128 enabledTransition := by
  have declarations : enabledGuardSource.declarations = [("x", .int)] := by
    native_decide
  have predicates : enabledGuardSource.predicates =
      [.bin "=" (.id "x") (.num 0)] := by
    native_decide
  unfold CheckedGuardSource.holds
  rw [declarations, predicates]
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · intro predicate member
    simp only [List.mem_singleton] at member
    subst predicate
    unfold assignmentPredicateWithFuel
    native_decide

private theorem disabledGuardNotHolds :
    ¬ enabledGuardSource.holds 128 disabledTransition := by
  intro holds
  have predicates : enabledGuardSource.predicates =
      [.bin "=" (.id "x") (.num 0)] := by
    native_decide
  unfold CheckedGuardSource.holds at holds
  rw [predicates] at holds
  rcases holds with ⟨_, _, _, predicate⟩
  have falsePredicate := predicate (.bin "=" (.id "x") (.num 0)) (by simp)
  unfold assignmentPredicateWithFuel at falsePredicate
  have notTrue :
      evalBeforeAfter 128 disabledTransition
          (.bin "=" (.id "x") (.num 0)) ≠ .ok true := by
    native_decide
  exact notTrue falsePredicate

private def enabledEvent : Event CheckedBeforeAfter :=
  { grd := fun transition => enabledGuardSource.holds 128 transition
    act := fun before _ => enabledEventSource.assignmentAction 128 before }

private def badGuardEvent : Event CheckedBeforeAfter :=
  { grd := fun _ => True
    act := fun before _ => enabledEventSource.assignmentAction 128 before }

private theorem actionProvenance :
    eventActionExact enabledEventSource 128
      (fun state : CheckedBeforeAfter × CheckedBeforeAfter => state.1)
      (fun state => enabledEvent.act state.1 state.2) := by
  intro state
  rfl

private theorem guardProvenance :
    ∀ transition, enabledEvent.grd transition ↔
      enabledGuardSource.holds 128 transition := by
  intro transition
  rfl

private theorem enabledEvent_is_enabled : enabledEvent.grd enabledTransition ∧
    enabledEvent.act enabledTransition enabledTransition := by
  exact ⟨enabledGuard, enabledAction⟩

private theorem enabledEvent_is_disabled : ¬ enabledEvent.grd disabledTransition :=
  disabledGuardNotHolds

example : enabledEvent.act disabledTransition disabledTransition := by
  exact disabledAction

example : ¬ (∀ transition,
    badGuardEvent.grd transition ↔ enabledGuardSource.holds 128 transition) := by
  intro exactness
  have mismatch := exactness disabledTransition
  apply disabledGuardNotHolds
  simpa [badGuardEvent] using mismatch.mp trivial

/- A model-derived parameterized event.  The parameter is part of the checked
   lexical environment, while the action still reads it from the pre-state and
   updates only the declared machine variable. -/

private def parameterizedEventProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [ ("org.eventb.core.name", "M") ]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "x ∈ ℤ")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 0")] [] ]
       , .event [("org.eventb.core.label", "step")]
           [ .parameter [("org.eventb.core.identifier", "p")] []
           , .guard [("org.eventb.core.label", "enabled"),
                     ("org.eventb.core.predicate", "p > 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ p")] [] ] ] }]

#guard match generateCheckedIn EventB.Theory.empty parameterizedEventProject "M" with
  | .ok _ => true
  | .error _ => false

private def parameterizedEventSource :
    CheckedEventSource EventB.Theory.empty parameterizedEventProject "M" "step" :=
  (CheckedEventSource.fromProject EventB.Theory.empty parameterizedEventProject "M" "step").get
    (by native_decide)

private def parameterizedGuardSource :
    CheckedGuardSource EventB.Theory.empty parameterizedEventProject "M" "step" :=
  (CheckedGuardSource.fromProject EventB.Theory.empty parameterizedEventProject "M" "step").get
    (by native_decide)

#guard parameterizedEventSource.declarations == [("x", .int), ("p", .int)]
#guard parameterizedEventSource.updates == [("x", .id "p")]
#guard parameterizedGuardSource.declarations == [("x", .int), ("p", .int)]
#guard parameterizedGuardSource.predicates == [.bin ">" (.id "p") (.num 0)]

private def parameterizedTransition (parameter state after : Int) : CheckedBeforeAfter :=
  { before := { values := [("x", .integer state), ("p", .integer parameter)] }
    after := { values := [("x", .integer after), ("p", .integer parameter)] }
    declarations := [("x", .int), ("p", .int)] }

private def parameterizedEvent : ParameterizedEvent Int Int :=
  { grd := fun parameter _ => parameter > 0
    act := fun parameter _ after => after = parameter }

example : parameterizedEvent.enabled 0 := by
  exact ⟨1, by change (1 : Int) > 0; omega⟩

example : parameterizedEventSource.assignmentAction 128
    (parameterizedTransition 7 0 7) := by
  unfold CheckedEventSource.assignmentAction assignmentRelation
  native_decide

example : parameterizedGuardSource.holds 128
    (parameterizedTransition 7 0 7) := by
  have declarations : parameterizedGuardSource.declarations =
      [("x", .int), ("p", .int)] := by native_decide
  have predicates : parameterizedGuardSource.predicates =
      [.bin ">" (.id "p") (.num 0)] := by native_decide
  unfold CheckedGuardSource.holds
  rw [declarations, predicates]
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · intro predicate member
    simp only [List.mem_singleton] at member
    subst predicate
    unfold assignmentPredicateWithFuel
    native_decide

example : ¬ parameterizedGuardSource.holds 128
    (parameterizedTransition (-1) 0 (-1)) := by
  have predicates : parameterizedGuardSource.predicates =
      [.bin ">" (.id "p") (.num 0)] := by native_decide
  unfold CheckedGuardSource.holds
  intro holds
  rw [predicates] at holds
  rcases holds with ⟨_, _, _, predicate⟩
  have falsePredicate := predicate (.bin ">" (.id "p") (.num 0)) (by simp)
  unfold assignmentPredicateWithFuel at falsePredicate
  have notTrue :
      evalBeforeAfter 128 (parameterizedTransition (-1) 0 (-1))
          (.bin ">" (.id "p") (.num 0)) ≠ .ok true := by
    native_decide
  exact notTrue falsePredicate

private def abstractParameterizedEvent : ParameterizedEvent Nat Nat :=
  { grd := fun parameter _ => parameter > 0
    act := fun _ before after => after = before + 1 }

private def concreteParameterizedEvent : ParameterizedEvent Nat Nat :=
  { grd := fun parameter _ => parameter > 0
    act := fun _ before after => after = before + 1 }

private theorem parameterizedRefinement :
    ParameterizedEventRefinement concreteParameterizedEvent
      abstractParameterizedEvent (fun concrete abstract => concrete = abstract) :=
  { guard := by
      intro parameter concrete abstract glued guard
      subst abstract
      exact ⟨parameter, guard⟩
    action := by
      intro parameter concrete concreteAfter abstract glued guard action
      subst abstract
      exact ⟨parameter, concreteAfter, guard, action, rfl⟩ }

example : ∃ abstractAfter,
    abstractParameterizedEvent.step 1 abstractAfter ∧
      (2 = abstractAfter) := by
  obtain ⟨abstractAfter, step, glued⟩ :=
    parameterizedRefinement.stepSim 1 2 1 rfl
      (show concreteParameterizedEvent.step 1 2 from
        ⟨1, by change (1 : Nat) > 0; decide,
          by change (2 : Nat) = 1 + 1; decide⟩)
  exact ⟨abstractAfter, step, by simpa using glued⟩

private def naturalWellFoundedVariant : WellFoundedVariant Nat Nat :=
  { measure := id
    relation := (· < ·)
    wellFounded := Nat.lt_wfRel.wf
    action := fun before after => after < before
    progress := fun _ _ progress => progress }

example : wellFoundedVariantProgressSemantic naturalWellFoundedVariant :=
  naturalWellFoundedVariant.progressSemantic

end EventB.POG
