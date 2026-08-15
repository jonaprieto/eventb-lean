/- Complete source-bound EQL acceptance fixture. -/

import EventB.POG.EQLAdapter

namespace EventB.POG

private def eqlBinding : EqlIntBinding Theory.empty positiveProject :=
  (EqlIntBinding.fromProject? Theory.empty positiveProject "B" "step" "x").get
    (by native_decide)

#guard (EqlIntBinding.fromProject? Theory.empty positiveProject "B" "step" "y").isNone

private def eqlEncode (_ : Unit) : ValueEnv :=
  { values := [("x", .integer 0)] }

private def eqlTransition : CheckedBeforeAfter :=
  { before := eqlEncode ()
    after := eqlEncode ()
    declarations := [("x", .int)] }

private theorem eqlAssignment :
    ValueEnv.parallelAssignTypedFuel 128 [("x", .int)] (eqlEncode ())
      [("x", .id "x")] = .ok eqlTransition := by
  native_decide

private def eqlBridge : EqlIntEventBridge eqlBinding Unit :=
  { fuel := 128
    encode := eqlEncode
    event :=
      { grd := fun _ => True
        act := fun before after => eqlBinding.action 128
          (eqlEncode before) (eqlEncode after) }
    declarationsExact := by native_decide
    stateValid := by intro state; cases state; native_decide
    actionExact := by intro before after; exact Iff.rfl
    unprimed := by native_decide
    primedBase := by native_decide
    primeNotInteger := by native_decide
    primeNotNatural := by native_decide
    primeNotNatural1 := by native_decide
    primeNotBoolean := by native_decide
    notInteger := by native_decide
    notNatural := by native_decide
    notNatural1 := by native_decide
    notBoolean := by native_decide
    hypothesesHold := by
      intro before after eventStep
      cases before
      cases after
      change EqlIntBinding.action eqlBinding 128 (eqlEncode ()) (eqlEncode ()) at eventStep
      rcases eventStep with ⟨transition, computed, afterEq⟩
      have declarations : eqlBinding.declarations = [("x", .int)] := by
        native_decide
      have updates : eqlBinding.updates = [("x", .id "x")] := by
        native_decide
      rw [declarations, updates] at computed
      rw [eqlAssignment] at computed
      cases computed
      rw [declarations]
      refine ⟨eqlTransition, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro hypothesis membership
        have hypotheses : eqlBinding.obligation.hyps =
            [.bin "∈" (.id "x") (.id "ℤ"),
             .bin "∈" (.id "x") (.id "ℤ"), eqlGoal "x"] := by
          native_decide
        rw [hypotheses] at membership
        have cases : hypothesis = .bin "∈" (.id "x") (.id "ℤ") ∨
            hypothesis = .bin "∈" (.id "x") (.id "ℤ") ∨
            hypothesis = eqlGoal "x" := by
          simpa using membership
        rcases cases with h | h | h
        · rw [h]; simpa [eqlTransition, eqlEncode] using assignmentPredicate_x_in_integer_set
        · rw [h]; simpa [eqlTransition, eqlEncode] using assignmentPredicate_x_in_integer_set
        · rw [h]; simpa [eqlTransition, eqlEncode, eqlGoal] using assignmentPredicate_x_self_zero
    stateInteger := by
      intro state
      cases state
      exact ⟨0, by native_decide⟩
    nonempty := by
      have declarations : eqlBinding.declarations = [("x", .int)] := by
        native_decide
      have updates : eqlBinding.updates = [("x", .id "x")] := by
        native_decide
      refine ⟨(), (), ?_⟩
      change EqlIntBinding.action eqlBinding 128 (eqlEncode ()) (eqlEncode ())
      change ∃ transition, ValueEnv.parallelAssignTypedFuel 128 eqlBinding.declarations
        (eqlEncode ()) eqlBinding.updates = .ok transition ∧ transition.after = eqlEncode ()
      rw [declarations, updates]
      exact ⟨eqlTransition, eqlAssignment, rfl⟩ }

private def eqlAdapter : EqlIntAdapter Theory.empty positiveProject Unit :=
  { binding := eqlBinding
    bridge := eqlBridge
    sequent := eqlBridge.sequent_of_goal_hypothesis (by native_decide) }

example : framePreserved eqlAdapter.bridge.read eqlAdapter.bridge.event.act :=
  eqlAdapter.sound

end EventB.POG
