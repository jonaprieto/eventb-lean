/- Generated MRG acceptance fixture with source-bound branch pairing. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def mrgAdapterProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [ .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "left")]
           [ .guard [("org.eventb.core.label", "g0"),
                     ("org.eventb.core.predicate", "1 = 1")] [] ]
       , .event [("org.eventb.core.label", "right")]
           [ .guard [("org.eventb.core.label", "g1"),
                     ("org.eventb.core.predicate", "1 = 1")] [] ] ] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [ .refinesMachine [("org.eventb.core.target", "A")] []
         , .event [("org.eventb.core.label", "INITIALISATION")] []
         , .event [("org.eventb.core.label", "merge")]
             [ .refinesEvent [("org.eventb.core.target", "left")] []
             , .refinesEvent [("org.eventb.core.target", "right")] [] ] ] }]

private def mrgObligation : Obligation :=
  { component := "B"
    name := "merge/MRG"
    kind := "MRG"
    goal := some (.bin "∨"
      (.bin "=" (.num 1) (.num 1))
      (.bin "=" (.num 1) (.num 1))) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty mrgAdapterProject
  mrgObligation).isSome

private def mrgPO : CheckedPO EventB.Theory.empty mrgAdapterProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty mrgAdapterProject mrgObligation).get
    (by native_decide)

private def mrgEventSourceBound : CheckedEventSource EventB.Theory.empty
    mrgAdapterProject mrgPO.obligation.component "merge" := by
  have component : mrgPO.obligation.component = "B" := by native_decide
  rw [component]
  exact (CheckedEventSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgMergeSourceBound : CheckedMergeSource EventB.Theory.empty
    mrgAdapterProject mrgPO.obligation.component "merge" := by
  have component : mrgPO.obligation.component = "B" := by native_decide
  rw [component]
  exact (CheckedMergeSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgGuardSourceBound : CheckedGuardSource EventB.Theory.empty
    mrgAdapterProject mrgPO.obligation.component "merge" := by
  have component : mrgPO.obligation.component = "B" := by native_decide
  rw [component]
  exact (CheckedGuardSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgLeft : Event Unit :=
  { grd := fun _ => True
    act := fun _ _ => True }

private def mrgRight : Event Unit :=
  { grd := fun _ => True
    act := fun _ _ => True }

private def mrgEventSource : CheckedEventSource EventB.Theory.empty
    mrgAdapterProject "B" "merge" :=
  (CheckedEventSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgMergeSource : CheckedMergeSource EventB.Theory.empty
    mrgAdapterProject "B" "merge" :=
  (CheckedMergeSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgGuardSource : CheckedGuardSource EventB.Theory.empty
    mrgAdapterProject "B" "merge" :=
  (CheckedGuardSource.fromProject EventB.Theory.empty mrgAdapterProject "B" "merge").get
    (by native_decide)

private def mrgTransition : CheckedBeforeAfter :=
  { before := {}, after := {}, declarations := [] }

private def mrgLeftEventSource : CheckedEventSource EventB.Theory.empty
    mrgAdapterProject "A" "left" :=
  (CheckedEventSource.fromProject EventB.Theory.empty mrgAdapterProject "A" "left").get
    (by native_decide)

private def mrgRightEventSource : CheckedEventSource EventB.Theory.empty
    mrgAdapterProject "A" "right" :=
  (CheckedEventSource.fromProject EventB.Theory.empty mrgAdapterProject "A" "right").get
    (by native_decide)

private def mrgLeftGuardSource : CheckedGuardSource EventB.Theory.empty
    mrgAdapterProject "A" "left" :=
  (CheckedGuardSource.fromProject EventB.Theory.empty mrgAdapterProject "A" "left").get
    (by native_decide)

private def mrgRightGuardSource : CheckedGuardSource EventB.Theory.empty
    mrgAdapterProject "A" "right" :=
  (CheckedGuardSource.fromProject EventB.Theory.empty mrgAdapterProject "A" "right").get
    (by native_decide)

private theorem mrgLeftAssignment :
    mrgLeftEventSource.assignmentAction 128 mrgTransition := by
  change assignmentRelation 128 mrgLeftEventSource.declarations
    mrgTransition mrgLeftEventSource.updates
  have declarations : mrgLeftEventSource.declarations = [] := by native_decide
  have updates : mrgLeftEventSource.updates = [] := by native_decide
  rw [declarations, updates]
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

private theorem mrgRightAssignment :
    mrgRightEventSource.assignmentAction 128 mrgTransition := by
  change assignmentRelation 128 mrgRightEventSource.declarations
    mrgTransition mrgRightEventSource.updates
  have declarations : mrgRightEventSource.declarations = [] := by native_decide
  have updates : mrgRightEventSource.updates = [] := by native_decide
  rw [declarations, updates]
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

private theorem mrgLeftGuardHolds :
    mrgLeftGuardSource.holds 128 mrgTransition := by
  have declarations : mrgLeftGuardSource.declarations = [] := by native_decide
  have predicates : mrgLeftGuardSource.predicates =
      [.bin "=" (.num 1) (.num 1)] := by native_decide
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

private theorem mrgRightGuardHolds :
    mrgRightGuardSource.holds 128 mrgTransition := by
  have declarations : mrgRightGuardSource.declarations = [] := by native_decide
  have predicates : mrgRightGuardSource.predicates =
      [.bin "=" (.num 1) (.num 1)] := by native_decide
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

private def mrgLeftBinding : CheckedMergeBranch EventB.Theory.empty
    mrgAdapterProject Unit :=
  { locator := ("A", "left")
    eventSource := mrgLeftEventSource
    guardSource := mrgLeftGuardSource
    event := mrgLeft
    fuel := 128
    encode := fun _ => mrgTransition
    actionExact := by
      intro _
      constructor
      · intro _
        exact mrgLeftAssignment
      · intro _
        trivial
    guardExact := by
      intro _
      constructor
      · intro _
        exact mrgLeftGuardHolds
      · intro _
        trivial }

private def mrgRightBinding : CheckedMergeBranch EventB.Theory.empty
    mrgAdapterProject Unit :=
  { locator := ("A", "right")
    eventSource := mrgRightEventSource
    guardSource := mrgRightGuardSource
    event := mrgRight
    fuel := 128
    encode := fun _ => mrgTransition
    actionExact := by
      intro _
      constructor
      · intro _
        exact mrgRightAssignment
      · intro _
        trivial
    guardExact := by
      intro _
      constructor
      · intro _
        exact mrgRightGuardHolds
      · intro _
        trivial }

private def mrgBranchBindings : List (CheckedMergeBranch EventB.Theory.empty
    mrgAdapterProject Unit) :=
  [mrgLeftBinding, mrgRightBinding]

private theorem mrgAssignment :
    mrgEventSourceBound.assignmentAction 128 mrgTransition := by
  change assignmentRelation 128 mrgEventSourceBound.declarations
    mrgTransition mrgEventSourceBound.updates
  have declarations : mrgEventSourceBound.declarations = [] := by native_decide
  have updates : mrgEventSourceBound.updates = [] := by native_decide
  rw [declarations, updates]
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

private abbrev mrgSourceState :=
  { transition : CheckedBeforeAfter //
      mrgEventSourceBound.assignmentAction 128 transition }

private def mrgState : mrgSourceState := ⟨mrgTransition, mrgAssignment⟩

private def mrgModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := mrgEventSourceBound.assignmentAction 128
    inhabited := ⟨mrgTransition, mrgAssignment⟩
    supports := fun _ => true }

private def mrgConcrete : Event mrgSourceState :=
  { grd := fun _ => True
    act := fun _ _ => True }

private def mrgAbstractMachine : Machine Unit :=
  { inv := fun _ => True
    init := fun _ => True
    events := [mrgLeft, mrgRight] }

private def mrgConcreteMachine : Machine mrgSourceState :=
  { inv := fun _ => True
    init := fun _ => True
    events := [mrgConcrete] }

private def mrgContract : SplitSimulation mrgConcreteMachine mrgAbstractMachine
    (fun _ _ => True) :=
  { concreteEvent := mrgConcrete
    concreteMember := by simp [mrgConcreteMachine]
    abstractEvents := [mrgLeft, mrgRight]
    abstractNonempty := by simp
    abstractMember := by
      intro abstract member
      have branches : abstract = mrgLeft ∨ abstract = mrgRight := by
        simpa using member
      rcases branches with rfl | rfl <;> simp [mrgAbstractMachine]
    guard := by
      intro _ _ _ _
      exact ⟨mrgLeft, by simp, trivial⟩
    action := by
      intro abstract _ _ _ member _ _ _ _
      have branches : abstract = mrgLeft ∨ abstract = mrgRight := by
        simpa using member
      rcases branches with rfl | rfl <;> exact ⟨(), trivial, trivial⟩ }

private def mrgBranches : List (String × Event Unit) :=
  [("left", mrgLeft), ("right", mrgRight)]

private theorem mrgSemantic :
    splitSimulationSemantic mrgContract mrgBranches := by
  intro _ _ _ _ _ _
  exact ⟨"left", mrgLeft, (), by simp [mrgBranches], trivial, trivial, trivial⟩

private def mrgAdapter : MergeAdapter EventB.Theory.empty mrgAdapterProject
    (C := mrgConcreteMachine) (A := mrgAbstractMachine) (J := fun _ _ => True) :=
  { binding := mrgPO
    eventLabel := "merge"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := mrgEventSourceBound
    mergeSource := mrgMergeSourceBound
    guardSource := mrgGuardSourceBound
    contract := mrgContract
    branchBindings := mrgBranchBindings
    branchBindingLocatorsExact := by native_decide
    branchBindingObjectsExact := by rfl
    branchEvents := mrgBranches
    branchLabelsExact := by native_decide
    branchObjectsExact := by rfl
    branchBindingEventsExact := by rfl
    fuel := 128
    formula :=
      { evaluator := mrgModel
        encode := fun state => state.1.1.1
        declarations := []
        declarationScope := some "merge"
        declarationsBound := by
          have component : mrgPO.obligation.component = "B" := by native_decide
          rw [component]
          change exactEventDeclarations? EventB.Theory.empty mrgAdapterProject
            "B" "merge" = some []
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.1.2 with ⟨declared, _, _, _⟩
          have sourceDeclarations : mrgEventSourceBound.declarations = [] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by
          intro state
          exact state.1.1.2
        sourceValid := by
          intro state
          exact state.1.1.2
        sourceComplete := by
          intro transition source
          exact ⟨((⟨transition, source⟩, mrgState), ()), rfl⟩
        evaluatorValid := by
          simpa only [show mrgPO.obligation = mrgObligation by native_decide] using
            (typedTransitionModel_closed_validOnDomain mrgModel
              (mrgEventSourceBound.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact ⟨by simpa [declared] using beforeValid,
                  by simpa [declared] using afterValid⟩)
              mrgObligation (by native_decide) (by native_decide)
              (.bin "∨" (.bin "=" (.num 1) (.num 1))
                (.bin "=" (.num 1) (.num 1))) (by native_decide) (by native_decide)
              (by rfl) (by rfl)
              (by
                intro transition source
                have beforeValid :
                    ValueEnv.validationOk 128 transition.declarations transition.before = true := by
                  rcases source with ⟨declared, beforeValid, _, _⟩
                  simpa [declared] using beforeValid
                have afterValid :
                    ValueEnv.validationOk 128 transition.declarations transition.after = true := by
                  rcases source with ⟨declared, _, afterValid, _⟩
                  simpa [declared] using afterValid
                exact evalBeforeAfterIntegerOneOrOne transition beforeValid afterValid))
        adequate := by
          intro _
          exact mrgSemantic }
    fuelExact := by rfl
    actionExact := by
      intro state
      constructor
      · intro _
        exact state.1.1.2
      · intro _
        trivial
    guardExact := by
      intro state
      have declarations : mrgGuardSourceBound.declarations = [] := by native_decide
      have predicates : mrgGuardSourceBound.predicates = [] := by native_decide
      have source : mrgEventSourceBound.declarations = [] := by native_decide
      rcases state.1.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
      constructor
      · intro _
        unfold CheckedGuardSource.holds
        rw [declarations, predicates]
        constructor
        · simpa [source] using declared
        constructor
        · simpa [source] using beforeValid
        constructor
        · simpa [source] using afterValid
        · simp
      · intro _
        trivial }

example : ∀ c c' a, True → mrgAdapter.contract.concreteEvent.grd c →
    mrgAdapter.contract.concreteEvent.act c c' →
      ∃ label branch a', (label, branch) ∈ mrgAdapter.branchEvents ∧
        branch.grd a ∧ branch.act a a' ∧ True :=
  mrgAdapter.sound

end EventB.POG
