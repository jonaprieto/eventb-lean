/- Restricted-domain finite-set variant fixture. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def modelFiniteProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "S")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "S ∈ ℙ(ℤ)")] []
       , .invariant [("org.eventb.core.label", "finite"),
                    ("org.eventb.core.predicate", "finite(S)")] []
       , .variant [("org.eventb.core.expression", "S")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "hold"),
                 ("org.eventb.core.convergence", "2")] [] ] }]

private def parsed? (source : String) : Option EventB.Formula.Term :=
  (EventB.Formula.parse source).toOption

private def modelFinObligation : Obligation :=
  { component := "M", name := "FIN", kind := "FIN"
    goal := parsed? "finite(S)"
    hyps := [(parsed? "S ∈ ℙ(ℤ)").get (by native_decide),
      (parsed? "finite(S)").get (by native_decide)] }

private def modelVarObligation : Obligation :=
  { component := "M", name := "hold/VAR", kind := "VAR"
    goal := parsed? "S ⊆ S"
    hyps := [(parsed? "S ∈ ℙ(ℤ)").get (by native_decide),
      (parsed? "finite(S)").get (by native_decide)] }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty modelFiniteProject
  modelFinObligation).isSome
#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty modelFiniteProject
  modelVarObligation).isSome
#guard EventB.POG.eventRefinementTargets modelFiniteProject "M" "hold" == []

private def modelFinPO : CheckedPO EventB.Theory.empty modelFiniteProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty modelFiniteProject modelFinObligation).get
    (by native_decide)

private def modelVarPO : CheckedPO EventB.Theory.empty modelFiniteProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty modelFiniteProject modelVarObligation).get
    (by native_decide)

private def modelEventSource : CheckedEventSource EventB.Theory.empty
    modelFiniteProject "M" "hold" :=
  (CheckedEventSource.fromProject EventB.Theory.empty modelFiniteProject "M" "hold").get
    (by native_decide)

private def modelVariantSource : CheckedVariantSource modelFiniteProject "M" :=
  (CheckedVariantSource.fromProject modelFiniteProject "M").get (by native_decide)

private def modelEventSourceBound : CheckedEventSource EventB.Theory.empty
    modelFiniteProject modelFinPO.obligation.component "hold" := by
  have component : modelFinPO.obligation.component = "M" := by native_decide
  rw [component]
  exact modelEventSource

private def modelVariantSourceBound : CheckedVariantSource modelFiniteProject
    modelFinPO.obligation.component := by
  have component : modelFinPO.obligation.component = "M" := by native_decide
  rw [component]
  exact modelVariantSource

private def modelDeclarations : List (String × EventB.Typing.Ty) :=
  [("S", .pow .int)]

private def modelTypeGoal : EventB.Formula.Term :=
  .bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))

private def modelFiniteGoal : EventB.Formula.Term :=
  .app (.id "finite") (.id "S")

private def modelShape (env : ValueEnv) : Prop :=
  ∃ values, evalValueAtFuel 127 env (.id "S") = .ok (.set values)

private def modelFinObligationExact : Obligation :=
  { component := "M", name := "FIN", kind := "FIN"
    goal := some modelFiniteGoal
    hyps := [modelTypeGoal, modelFiniteGoal] }

private def modelDomain (env : ValueEnv) : Prop :=
  ValueEnv.validationOk 128 modelDeclarations env = true ∧
    evalPredicateAtFuel 128 env modelTypeGoal = .ok true ∧
    evalPredicateAtFuel 128 env modelFiniteGoal = .ok true ∧
    modelShape env

private abbrev modelState := { env : ValueEnv // modelDomain env }

private theorem modelValidationFuelOfOk (env : ValueEnv)
    (h : ValueEnv.validationOk 128 modelDeclarations env = true) :
    ValueEnv.validateFuel 128 modelDeclarations env = .ok PUnit.unit := by
  unfold ValueEnv.validationOk at h
  cases result : ValueEnv.validateFuel 128 modelDeclarations env with
  | error error => simp [result] at h
  | ok value => cases value; simpa using result

private def modelFormulaModel : TypedFormulaModel :=
  { declarations := modelDeclarations
    fuel := 128
    wellFormed := fun env => ValueEnv.validationOk 128 modelDeclarations env = true
    inhabited := by
      refine ⟨{ values := [("S", .set [.integer 0])] }, ?_⟩
      native_decide
    validated := by
      intro env proof
      exact proof
    complete := by
      intro env proof
      exact proof
    supports := fun _ => true }

private def modelEncode (state : modelState) : ValueEnv := state.1

private def modelSourceTransition (state : modelState) : CheckedBeforeAfter :=
  { before := state.1, after := state.1, declarations := modelDeclarations }

private theorem modelSourceAssignment (state : modelState) :
    modelEventSourceBound.assignmentAction 128 (modelSourceTransition state) := by
  change assignmentRelation 128 modelEventSourceBound.declarations
    (modelSourceTransition state) modelEventSourceBound.updates
  have declarations : modelEventSourceBound.declarations = modelDeclarations := by
    native_decide
  have updates : modelEventSourceBound.updates = [] := by
    native_decide
  rw [declarations, updates]
  unfold assignmentRelation
  refine ⟨rfl, state.2.1, state.2.1, ?_⟩
  have validationFuel := modelValidationFuelOfOk state.1 state.2.1
  simp [modelSourceTransition, ValueEnv.parallelAssignTypedFuel,
    CheckedBeforeAfter.make, validationFuel, Bind.bind, Except.bind]
  rfl

private theorem modelSourceAfterEq (transition : CheckedBeforeAfter)
    (source : modelEventSourceBound.assignmentAction 128 transition) :
    transition.after = transition.before := by
  change assignmentRelation 128 modelEventSourceBound.declarations transition
    modelEventSourceBound.updates at source
  have declarations : modelEventSourceBound.declarations = modelDeclarations := by
    native_decide
  have updates : modelEventSourceBound.updates = [] := by
    native_decide
  rw [declarations, updates] at source
  rcases source with ⟨_, _, _, assigned⟩
  cases validation : ValueEnv.validateFuel 128 modelDeclarations transition.before with
  | error error =>
      simp [ValueEnv.parallelAssignTypedFuel, validation, Bind.bind, Except.bind] at assigned
  | ok _unit =>
      simp [ValueEnv.parallelAssignTypedFuel, CheckedBeforeAfter.make,
        validation, Bind.bind, Except.bind] at assigned
      change (Except.ok
          ({ before := transition.before, after := transition.before,
              declarations := modelDeclarations } : CheckedBeforeAfter)) =
        Except.ok transition at assigned
      have canonical :
          ({ before := transition.before, after := transition.before,
              declarations := modelDeclarations } : CheckedBeforeAfter) = transition := by
        injection assigned
      exact (congrArg CheckedBeforeAfter.after canonical).symm

private abbrev modelVarState :=
  { pair : modelState × modelState // pair.1.1 = pair.2.1 }

private def modelVarEncode (state : modelVarState) : CheckedBeforeAfter :=
  { before := state.1.1.1, after := state.1.2.1, declarations := modelDeclarations }

private def modelVarSource (transition : CheckedBeforeAfter) : Prop :=
  modelEventSourceBound.assignmentAction 128 transition ∧
    modelDomain transition.before ∧ modelDomain transition.after

private theorem modelVarSourceValid (state : modelVarState) :
    modelVarSource (modelVarEncode state) := by
  refine ⟨?_, state.1.1.2, state.1.2.2⟩
  simpa [modelVarEncode, modelSourceTransition, state.2] using
    modelSourceAssignment state.1.1

private theorem modelVarSourceComplete (transition : CheckedBeforeAfter)
    (source : modelVarSource transition) :
    ∃ state : modelVarState, modelVarEncode state = transition := by
  rcases source with ⟨assignment, beforeDomain, afterDomain⟩
  have afterEq := modelSourceAfterEq transition assignment
  refine ⟨⟨(⟨transition.before, beforeDomain⟩, ⟨transition.after, afterDomain⟩),
      afterEq.symm⟩, ?_⟩
  rcases assignment with ⟨declared, _, _, _⟩
  have declarations : modelEventSourceBound.declarations = modelDeclarations := by
    native_decide
  have declaredExact : transition.declarations = modelDeclarations :=
    declared.trans declarations
  cases transition
  simp [modelVarEncode]
  exact declaredExact.symm

private theorem modelSubsetSelfEval (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (shape : modelShape transition.before)
    (afterEq : transition.after = transition.before) :
    evalBeforeAfter 128 transition
      (.bin "⊆" (.id "S") (.id "S")) = .ok true := by
  exact evalBeforeAfterIdentifierSubsetSelf transition beforeValid afterValid shape afterEq

private def modelInitialState : modelState :=
  ⟨{ values := [("S", .set [.integer 0]) ] }, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · native_decide
    · native_decide
    · native_decide
    · refine ⟨[.integer 0], ?_⟩
      exact evalValueIdentifierSingletonZero⟩

private def modelInitialVarState : modelVarState :=
  ⟨(modelInitialState, modelInitialState), rfl⟩

private def modelVarEvaluator : TypedTransitionModel :=
  { fuel := 128
    wellFormed := modelVarSource
    inhabited := ⟨modelVarEncode modelInitialVarState, modelVarSourceValid modelInitialVarState⟩
    supports := fun _ => true }

private theorem modelVarEvaluatorValid :
    modelVarEvaluator.validOnDomain modelVarSource modelVarObligation := by
  have obligationExact : modelVarObligation =
      { component := "M", name := "hold/VAR", kind := "VAR"
        goal := some (.bin "⊆" (.id "S") (.id "S"))
        hyps := [modelTypeGoal, modelFiniteGoal] } := by native_decide
  rw [obligationExact]
  unfold TypedTransitionModel.validOnDomain
  have shape : modelVarObligation.semanticShapeValid = true := by native_decide
  have valuation : modelVarObligation.transitionValuationSupported = true := by native_decide
  constructor
  · constructor <;> native_decide
  · constructor
    · native_decide
    · intro transition source
      rcases source with ⟨assignment, beforeDomain, afterDomain⟩
      have afterEq := modelSourceAfterEq transition assignment
      rcases assignment with ⟨declared, beforeValid, afterValid, _⟩
      have beforeValid' :
          ValueEnv.validationOk 128 transition.declarations transition.before = true := by
        simpa [declared] using beforeValid
      have afterValid' :
          ValueEnv.validationOk 128 transition.declarations transition.after = true := by
        simpa [declared] using afterValid
      constructor
      · constructor
        · exact ⟨true, modelSubsetSelfEval transition beforeValid' afterValid'
            beforeDomain.2.2.2 afterEq⟩
        · intro hypothesis member
          simp at member
          rcases member with rfl | rfl
          · exact ⟨true, by
              exact evalBeforeAfterIdentifierType transition beforeValid' afterValid'
                beforeDomain.2.1⟩
          · exact ⟨true, by
              exact evalBeforeAfterIdentifierFinite transition beforeValid' afterValid'
                beforeDomain.2.2.1⟩
      · intro hypotheses
        exact modelSubsetSelfEval transition beforeValid' afterValid'
          beforeDomain.2.2.2 afterEq

private theorem modelFinEvaluatorValid :
    modelFormulaModel.validOnDomain modelDomain modelFinObligation := by
  have obligationExact : modelFinObligation =
      modelFinObligationExact := by native_decide
  rw [obligationExact]
  unfold TypedFormulaModel.validOnDomain
  constructor
  · constructor <;> native_decide
  · constructor
    · native_decide
    · intro env domain
      have typeValid : evalPredicateAtFuel 128 env modelTypeGoal = .ok true :=
        domain.2.1
      have finiteValid : evalPredicateAtFuel 128 env modelFiniteGoal = .ok true :=
        domain.2.2.1
      change
        ((∃ value, evalPredicateAtFuel 128 env modelFiniteGoal = .ok value) ∧
            (∀ hypothesis ∈ [modelTypeGoal, modelFiniteGoal],
              ∃ value, evalPredicateAtFuel 128 env hypothesis = .ok value)) ∧
          ((∀ hypothesis ∈ [modelTypeGoal, modelFiniteGoal],
              evalPredicateAtFuel 128 env hypothesis = .ok true) →
            evalPredicateAtFuel 128 env modelFiniteGoal = .ok true)
      constructor
      · constructor
        · exact ⟨true, finiteValid⟩
        · intro hypothesis member
          simp at member
          rcases member with rfl | rfl
          · exact ⟨true, typeValid⟩
          · exact ⟨true, finiteValid⟩
      · intro _
        exact finiteValid

private def modelFiniteVariant : FiniteSetVariant modelState Int :=
  { mode := .anticipated
    measure := fun state =>
      match evalValueAtFuel 128 state.1 (.id "S") with
      | .ok (.set values) => values.filterMap fun value =>
          match value with | .integer n => some n | _ => none
      | _ => []
    action := fun before after => before = after
    finite := fun _ => True
    progress := by
      intro before after action value member
      simpa [action] using member }

private theorem modelFinitenessExact : ∀ state : modelState,
    modelFiniteVariant.finite state ↔
      modelFormulaModel.denote modelFiniteGoal (modelEncode state) := by
  intro state
  constructor
  · intro _
    exact state.2.2.2.1
  · intro _
    trivial

private def modelFinFormula : DomainFormulaAdequacy modelFinPO modelState
    (finiteVariantFiniteness modelFiniteVariant) modelDomain :=
  { evaluator := modelFormulaModel
    encode := modelEncode
    declarationScope := none
    declarationsBound := by
      have component : modelFinPO.obligation.component = "M" := by native_decide
      rw [component]
      change exactComponentDeclarations? EventB.Theory.empty modelFiniteProject "M" =
        some modelDeclarations
      native_decide
    stateValid := by intro state; exact state.2
    stateComplete := by
      intro env domain
      exact ⟨⟨env, domain⟩, rfl⟩
    evaluatorValid := by
      simpa only [show modelFinPO.obligation = modelFinObligation by native_decide] using
        modelFinEvaluatorValid
    adequate := by
      intro valid state
      apply (modelFinitenessExact state).mpr
      have obligationExact : modelFinPO.obligation = modelFinObligationExact := by native_decide
      rw [obligationExact] at valid
      simp [FormulaModel.validUnchecked, TypedFormulaModel.on,
        modelFinObligationExact] at valid
      apply valid state
      intro hypothesis member
      simp at member
      rcases member with rfl | rfl
      · exact state.2.2.1
      · exact state.2.2.2.1 }

private def modelVarBefore (state : modelVarState) : modelState := state.1.1

private def modelVarAfter (state : modelVarState) : modelState := state.1.2

private def modelVarFormula : TransitionFormulaAdequacy modelVarPO modelVarState
    (∀ state : modelVarState,
      modelFiniteVariant.action (modelVarBefore state) (modelVarAfter state) →
        finiteVariantProgress .anticipated
          (modelFiniteVariant.measure (modelVarAfter state))
          (modelFiniteVariant.measure (modelVarBefore state)))
    modelVarSource :=
  { evaluator := modelVarEvaluator
    encode := modelVarEncode
    declarations := modelDeclarations
    declarationScope := some "hold"
    declarationsBound := by
      have component : modelVarPO.obligation.component = "M" := by native_decide
      rw [component]
      change exactEventDeclarations? EventB.Theory.empty modelFiniteProject "M" "hold" =
        some modelDeclarations
      native_decide
    transitionDeclarations := by intro _; rfl
    transitionValid := by intro state; exact modelVarSourceValid state
    sourceValid := by intro state; exact modelVarSourceValid state
    sourceComplete := modelVarSourceComplete
    evaluatorValid := by
      simpa only [show modelVarPO.obligation = modelVarObligation by native_decide] using
        modelVarEvaluatorValid
    adequate := by
      intro _ state action
      change state.1.1 = state.1.2 at action
      change finiteSubset
        (modelFiniteVariant.measure (modelVarAfter state))
        (modelFiniteVariant.measure (modelVarBefore state))
      intro value member
      simpa [modelVarBefore, modelVarAfter, action] using member }

private def modelRestrictedAdapter :
    RestrictedFiniteSetVariantAdapter (η := modelVarState) (γ := modelState)
      EventB.Theory.empty modelFiniteProject modelFiniteVariant :=
  { finBinding := modelFinPO
    varBinding := modelVarPO
    finKind := by native_decide
    varKind := by native_decide
    componentMatch := by native_decide
    eventLabel := "hold"
    eventSource := modelEventSourceBound
    variantSource := modelVariantSourceBound
    finName := by native_decide
    varName := by native_decide
    convergence := "2"
    convergenceExact := by native_decide
    modeExact := by rfl
    fuel := 128
    stateOf := id
    stateCoverage := by intro state; exact ⟨state, rfl⟩
    finGoalExact := by native_decide
    semanticDomain := modelDomain
    finFormula := modelFinFormula
    finitenessExact := by
      intro state
      have expression : modelVariantSourceBound.expression = .id "S" := by
        native_decide
      simpa [expression, modelFinFormula, modelFiniteGoal, modelEncode,
        TypedFormulaModel.denote] using modelFinitenessExact state
    varState := modelVarState
    varBefore := modelVarBefore
    varAfter := modelVarAfter
    varSource := modelVarSource
    varSourceExact := by intro _; rfl
    varFormula := modelVarFormula
    varPairCoverage := by
      intro before after action
      change before = after at action
      cases action
      exact ⟨⟨(before, before), rfl⟩, rfl, rfl⟩
    varActionExact := by
      intro state
      constructor
      · intro _
        exact modelVarSourceValid state
      · intro source
        rcases source with ⟨assignment, _, _⟩
        have afterEq := modelSourceAfterEq (modelVarEncode state) assignment
        apply Subtype.ext
        simpa [modelVarBefore, modelVarAfter, modelVarEncode] using afterEq.symm
    fuelExact := by constructor <;> rfl }

private theorem modelRestrictedSound :
    finiteVariantFiniteness modelFiniteVariant ∧
      finiteVariantProgressSemantic modelFiniteVariant :=
  RestrictedFiniteSetVariantAdapter.sound modelRestrictedAdapter

example : ¬ finiteVariantProgress .convergent ([0] : List Int) [0] := by
  intro progress
  rcases progress.2 with ⟨value, member, absent⟩
  simp_all

end EventB.POG
