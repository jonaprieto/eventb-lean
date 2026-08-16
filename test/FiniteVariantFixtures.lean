/- Source-bound finite-set variant fixture. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def finiteVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "S")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "S ∈ ℙ(ℤ)")] []
       , .variant [("org.eventb.core.expression", "S")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "S ≔ {0, 1}")] [] ]
       , .event [("org.eventb.core.label", "step"),
                 ("org.eventb.core.convergence", "1")]
           [ .guard [("org.eventb.core.label", "nonempty"),
                     ("org.eventb.core.predicate", "S ≠ ∅")] []
           , .action [("org.eventb.core.label", "remove"),
                      ("org.eventb.core.assignment", "S ≔ S ∖ {0}")] [] ] ] }]

private def parsed? (source : String) : Option EventB.Formula.Term :=
  (EventB.Formula.parse source).toOption

#guard match generateCheckedIn EventB.Theory.empty finiteVariantProject "M" with
  | .ok obligations =>
      obligations.any (fun obligation => obligation.kind == "FIN" &&
        obligation.goal == parsed? "finite(S)")
  | .error _ => false

#guard match generateCheckedIn EventB.Theory.empty finiteVariantProject "M" with
  | .ok obligations =>
      obligations.any (fun obligation => obligation.kind == "VAR" &&
        obligation.name == "step/VAR" &&
        obligation.goal == parsed? "S ∖ {0} ⊂ S")
  | .error _ => false

#guard EventB.POG.eventConvergenceMode? finiteVariantProject "M" "step" == some "1"
#guard EventB.POG.eventConvergenceMode? finiteVariantProject "M" "missing" == none

private def anticipatedFiniteVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "S")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "S ∈ ℙ(ℤ)")] []
       , .invariant [("org.eventb.core.label", "finite"),
                    ("org.eventb.core.predicate", "finite(S)")] []
       , .variant [("org.eventb.core.expression", "S")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "S ≔ {0, 1}")] [] ]
       , .event [("org.eventb.core.label", "hold"),
                 ("org.eventb.core.convergence", "2")]
           [ .action [("org.eventb.core.label", "hold"),
                      ("org.eventb.core.assignment", "S ≔ S")] [] ] ] }]

private def anticipatedFinObligation : Obligation :=
  { component := "M", name := "FIN", kind := "FIN"
    goal := parsed? "finite(S)"
    hyps := [(parsed? "S ∈ ℙ(ℤ)").get (by native_decide),
      (parsed? "finite(S)").get (by native_decide)] }

private def anticipatedVarObligation : Obligation :=
  { component := "M", name := "hold/VAR", kind := "VAR"
    goal := parsed? "S ⊆ S"
    hyps := [(parsed? "S ∈ ℙ(ℤ)").get (by native_decide),
      (parsed? "finite(S)").get (by native_decide)] }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty anticipatedFiniteVariantProject
  anticipatedFinObligation).isSome
#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty anticipatedFiniteVariantProject
  anticipatedVarObligation).isSome
#guard EventB.POG.eventConvergenceMode? anticipatedFiniteVariantProject "M" "hold" == some "2"

private def anticipatedFinPO : CheckedPO EventB.Theory.empty anticipatedFiniteVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty anticipatedFiniteVariantProject
    anticipatedFinObligation).get (by native_decide)

private def anticipatedVarPO : CheckedPO EventB.Theory.empty anticipatedFiniteVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty anticipatedFiniteVariantProject
    anticipatedVarObligation).get (by native_decide)

private def anticipatedEventSource : CheckedEventSource EventB.Theory.empty
    anticipatedFiniteVariantProject "M" "hold" :=
  (CheckedEventSource.fromProject EventB.Theory.empty anticipatedFiniteVariantProject
    "M" "hold").get (by native_decide)

private def anticipatedVariantSource : CheckedVariantSource anticipatedFiniteVariantProject "M" :=
  (CheckedVariantSource.fromProject anticipatedFiniteVariantProject "M").get (by native_decide)

#guard anticipatedEventSource.declarations == [("S", .pow .int)]
#guard anticipatedEventSource.updates == [("S", .id "S")]
#guard anticipatedVariantSource.expression == .id "S"

private def constantFiniteVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variant [("org.eventb.core.expression", "{0}")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "hold"),
                 ("org.eventb.core.convergence", "2")] [] ] }]

private def constantFinObligation : Obligation :=
  { component := "M", name := "FIN", kind := "FIN"
    goal := some (.app (.id "finite") (.set [.num 0])) }

private def constantVarObligation : Obligation :=
  { component := "M", name := "hold/VAR", kind := "VAR"
    goal := some (.bin "⊆" (.set [.num 0]) (.set [.num 0])) }

#guard match generateCheckedIn EventB.Theory.empty constantFiniteVariantProject "M" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.kind == "FIN" && obligation.goal == parsed? "finite({0})")
  | .error _ => false
#guard match generateCheckedIn EventB.Theory.empty constantFiniteVariantProject "M" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.kind == "VAR" && obligation.goal == parsed? "{0} ⊆ {0}")
  | .error _ => false

private def constantFinPO : CheckedPO EventB.Theory.empty constantFiniteVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantFiniteVariantProject
    constantFinObligation).get (by native_decide)

private def constantVarPO : CheckedPO EventB.Theory.empty constantFiniteVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantFiniteVariantProject
    constantVarObligation).get (by native_decide)

private def constantFinPOExact : CheckedPO EventB.Theory.empty constantFiniteVariantProject :=
  { obligation := constantFinObligation
    checked := by
      simpa only [show constantFinPO.obligation = constantFinObligation by native_decide] using
        constantFinPO.checked }

private def constantVarPOExact : CheckedPO EventB.Theory.empty constantFiniteVariantProject :=
  { obligation := constantVarObligation
    checked := by
      simpa only [show constantVarPO.obligation = constantVarObligation by native_decide] using
        constantVarPO.checked }

private def constantFiniteEventSource : CheckedEventSource EventB.Theory.empty
    constantFiniteVariantProject "M" "hold" :=
  (CheckedEventSource.fromProject EventB.Theory.empty constantFiniteVariantProject
    "M" "hold").get (by native_decide)

private def constantFiniteVariantSource : CheckedVariantSource constantFiniteVariantProject "M" :=
  (CheckedVariantSource.fromProject constantFiniteVariantProject "M").get (by native_decide)

#guard constantFiniteEventSource.declarations == []
#guard constantFiniteEventSource.updates == []
#guard constantFiniteVariantSource.expression == .set [.num 0]

private def constantFiniteTransition : CheckedBeforeAfter :=
  { before := {}, after := {}, declarations := [] }

private def constantFiniteEventSourceBound : CheckedEventSource EventB.Theory.empty
    constantFiniteVariantProject constantFinPOExact.obligation.component "hold" := by
  change CheckedEventSource EventB.Theory.empty constantFiniteVariantProject "M" "hold"
  exact constantFiniteEventSource

private def constantFiniteVariantSourceBound : CheckedVariantSource constantFiniteVariantProject
    constantFinPOExact.obligation.component := by
  change CheckedVariantSource constantFiniteVariantProject "M"
  exact constantFiniteVariantSource

private theorem constantFiniteAssignment :
    constantFiniteEventSource.assignmentAction 128 constantFiniteTransition := by
  change assignmentRelation 128 constantFiniteEventSource.declarations
    constantFiniteTransition constantFiniteEventSource.updates
  have declarations : constantFiniteEventSource.declarations = [] := by native_decide
  have updates : constantFiniteEventSource.updates = [] := by native_decide
  rw [declarations, updates]
  unfold assignmentRelation
  native_decide

private abbrev constantFiniteSourceState :=
  { transition : CheckedBeforeAfter //
      constantFiniteEventSourceBound.assignmentAction 128 transition }

private def constantFiniteSourceStateValue : constantFiniteSourceState :=
  ⟨constantFiniteTransition, by
    exact constantFiniteAssignment⟩

private theorem validationFuelOfOk (env : ValueEnv)
    (h : ValueEnv.validationOk 128 [] env = true) :
    ValueEnv.validateFuel 128 [] env = .ok PUnit.unit := by
  unfold ValueEnv.validationOk at h
  cases result : ValueEnv.validateFuel 128 [] env with
  | error error => simp [result] at h
  | ok value => cases value; simpa using result

private def constantFiniteFormulaModel : TypedFormulaModel :=
  { declarations := []
    fuel := 128
    wellFormed := fun env => ValueEnv.validateFuel 128 [] env = .ok PUnit.unit
    inhabited := ⟨{}, rfl⟩
    validated := by
      intro env proof
      unfold ValueEnv.validationOk
      rw [proof]
    complete := by intro env h; exact validationFuelOfOk env h
    supports := fun _ => true }

private abbrev constantFiniteFormulaState :=
  { env : ValueEnv // ValueEnv.validateFuel 128 [] env = .ok PUnit.unit }

private theorem constantFiniteFormulaValid :
    TypedFormulaModel.validUnchecked constantFiniteFormulaModel constantFinObligation := by
  constructor
  · native_decide
  constructor
  · rfl
  · intro env _
    constructor
    · constructor
      · refine ⟨true, evalPredicateFiniteZero env⟩
      · intro hypothesis member
        cases member
    · intro _
      exact evalPredicateFiniteZero env

private def constantFiniteTransitionModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := fun _ => True
    inhabited := ⟨constantFiniteTransition, trivial⟩
    supports := fun _ => true }

private abbrev constantFiniteSemanticState :=
  { env : ValueEnv // ValueEnv.validateFuel 128 [] env = .ok PUnit.unit }

private def constantFiniteStateOf (state : constantFiniteSourceState) :
    constantFiniteSemanticState := by
  refine ⟨state.1.before, ?_⟩
  rcases state.property with ⟨declared, beforeValid, _, _⟩
  have sourceDeclarations : constantFiniteEventSourceBound.declarations = [] := by native_decide
  have beforeValid' : ValueEnv.validationOk 128 [] state.1.before = true := by
    simpa [sourceDeclarations, declared] using beforeValid
  exact validationFuelOfOk _ beforeValid'

private def constantFiniteVariant : FiniteSetVariant constantFiniteSemanticState Int :=
  { mode := .anticipated
    measure := fun _ => [0]
    action := fun _ _ => True
    finite := fun _ => True
    progress := by
      intro _ _ _ value member
      simpa using member }

private def constantFiniteAdapter : FiniteSetVariantAdapter (γ := constantFiniteSourceState)
    EventB.Theory.empty constantFiniteVariantProject constantFiniteVariant :=
  { finBinding := constantFinPOExact
    varBinding := constantVarPOExact
    finKind := by native_decide
    varKind := by native_decide
    componentMatch := by native_decide
    eventLabel := "hold"
    eventSource := constantFiniteEventSourceBound
    variantSource := constantFiniteVariantSourceBound
    finName := by native_decide
    varName := by native_decide
    convergence := "2"
    convergenceExact := by native_decide
    modeExact := by rfl
    fuel := 128
    stateOf := constantFiniteStateOf
    stateCoverage := by
      intro state
      let transition : CheckedBeforeAfter :=
        { before := state.1, after := state.1, declarations := [] }
      have validation : ValueEnv.validationOk 128 [] state.1 = true := by
        unfold ValueEnv.validationOk
        rw [state.2]
      have validationFuel := validationFuelOfOk _ validation
      have assignment : constantFiniteEventSourceBound.assignmentAction 128 transition := by
        change assignmentRelation 128 constantFiniteEventSourceBound.declarations transition
          constantFiniteEventSourceBound.updates
        have declarations : constantFiniteEventSourceBound.declarations = [] := by native_decide
        have updates : constantFiniteEventSourceBound.updates = [] := by native_decide
        rw [declarations, updates]
        unfold assignmentRelation
        refine ⟨rfl, validation, validation, ?_⟩
        dsimp [transition]
        simp [ValueEnv.parallelAssignTypedFuel, CheckedBeforeAfter.make,
          validationFuel, Bind.bind, Except.bind]
        rfl
      refine ⟨⟨transition, assignment⟩, ?_⟩
      apply Subtype.ext
      rfl
    finFormula :=
      { evaluator := constantFiniteFormulaModel
        encode := fun state => state.1
        declarationScope := none
        declarationsBound := by
          have component : constantFinPOExact.obligation.component = "M" := by native_decide
          rw [component]
          change exactComponentDeclarations? EventB.Theory.empty
            constantFiniteVariantProject "M" = some []
          native_decide
        stateValid := by intro state; exact state.2
        stateComplete := by
          intro env h
          exact ⟨⟨env, h⟩, rfl⟩
        evaluatorValid := by
          simpa only [show constantFinPOExact.obligation = constantFinObligation by rfl] using
            constantFiniteFormulaValid
        adequate := by
          intro _ state
          trivial }
    varFormula :=
      { evaluator := constantFiniteTransitionModel
        encode := fun state => state.1.1
        declarations := []
        declarationScope := some "hold"
        declarationsBound := by
          have component : constantVarPOExact.obligation.component = "M" := by native_decide
          rw [component]
          change exactEventDeclarations? EventB.Theory.empty
            constantFiniteVariantProject "M" "hold" = some []
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.property with ⟨declared, _, _, _⟩
          have sourceDeclarations : constantFiniteEventSourceBound.declarations = [] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by intro _; trivial
        sourceValid := by intro state; exact state.1.property
        sourceComplete := by
          intro transition source
          exact ⟨(⟨transition, source⟩, constantFiniteSourceStateValue), rfl⟩
        evaluatorValid := by
          simpa only [show constantVarPOExact.obligation = constantVarObligation by rfl] using
            (typedTransitionModel_closed_validOnDomain constantFiniteTransitionModel
              (constantFiniteEventSourceBound.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact ⟨by simpa [declared] using beforeValid,
                  by simpa [declared] using afterValid⟩)
              constantVarObligation (by native_decide) (by native_decide)
              (.bin "⊆" (.set [.num 0]) (.set [.num 0])) (by native_decide)
              (by native_decide) (by rfl) (by rfl)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact evalBeforeAfterZeroSetSubset transition
                  (by simpa [declared] using beforeValid)
                  (by simpa [declared] using afterValid)))
        adequate := by
          intro _ state
          intro _
          change finiteSubset [0] [0]
          intro value member
          exact member }
    decodeVariantValue := fun value =>
      match value with
      | .integer value => some value
      | _ => none
    measureExact := by
      intro state
      have expression : constantFiniteVariantSourceBound.expression = .set [.num 0] := by
        native_decide
      rw [expression]
      rw [evalValueFiniteZero]
      rfl
    fuelExact := by constructor <;> rfl
    varActionExact := by
      intro state
      constructor
      · intro _
        exact state.1.property
      · intro _
        trivial }

example : finiteVariantFiniteness constantFiniteVariant ∧
    finiteVariantProgressSemantic constantFiniteVariant :=
  constantFiniteAdapter.sound

end EventB.POG
