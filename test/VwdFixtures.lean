/-
  Exact-source VWD fixture kept separate from the large integer-variant fixture.
  The split keeps Lake's C backend reproducible while retaining kernel-checked
  source binding and semantic adequacy coverage.
-/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def vwdFixtureProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variant [("org.eventb.core.expression", "0 ÷ 1")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] [] ] }]

private def positiveVwdObligation : Obligation :=
  { component := "M", name := "VWD", kind := "VWD"
    goal := some (.bin "≠" (.num 1) (.num 0)) }

private def positiveVwdPO : CheckedPO EventB.Theory.empty vwdFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty vwdFixtureProject
    positiveVwdObligation).get (by native_decide)

private def positiveVwdPOExact : CheckedPO EventB.Theory.empty vwdFixtureProject :=
  { obligation := positiveVwdObligation
    checked := by
      simpa only [show positiveVwdPO.obligation = positiveVwdObligation by native_decide] using
        positiveVwdPO.checked }

private def positiveVwdSource : CheckedVariantSource vwdFixtureProject "M" :=
  (CheckedVariantSource.fromProject vwdFixtureProject "M").get (by native_decide)

private def vwdFormulaModel : TypedFormulaModel :=
  { declarations := []
    fuel := 128
    wellFormed := fun env => ValueEnv.validationOk 128 [] env = true
    inhabited := ⟨{}, by native_decide⟩
    validated := fun _ proof => proof
    complete := fun _ proof => proof
    supports := fun _ => true }

private abbrev vwdState :=
  { env : ValueEnv // ValueEnv.validationOk 128 [] env = true }

private theorem vwdFormulaModel_valid :
    TypedFormulaModel.validUnchecked vwdFormulaModel positiveVwdObligation := by
  constructor
  · native_decide
  constructor
  · rfl
  · intro env _
    constructor
    · constructor
      · refine ⟨true, evalPredicateIntegerOneNeZero env⟩
      · intro hypothesis member
        cases member
    · intro _
      exact evalPredicateIntegerOneNeZero env

private def positiveVwdAdapter : VwdAdapter EventB.Theory.empty
    vwdFixtureProject vwdState :=
  { binding := positiveVwdPOExact
    kind := by native_decide
    sourceName := by native_decide
    variantSource := positiveVwdSource
    pre := fun _ => True
    defined := fun _ => True
    formula :=
      { evaluator := vwdFormulaModel
        encode := fun state => state.1
        declarationScope := none
        declarationsBound := by
          change exactComponentDeclarations? EventB.Theory.empty vwdFixtureProject "M" =
            some []
          native_decide
        stateValid := by intro state; exact state.2
        stateComplete := by
          intro env proof
          exact ⟨⟨env, proof⟩, rfl⟩
        evaluatorValid := by
          simpa only [show positiveVwdPOExact.obligation = positiveVwdObligation by rfl] using
            vwdFormulaModel_valid
        adequate := by intro _ _ _; trivial }
    nonempty := ⟨⟨{}, by native_decide⟩, trivial⟩ }

example : witnessDefinednessSemantic positiveVwdAdapter.pre positiveVwdAdapter.defined :=
  positiveVwdAdapter.sound

end EventB.POG
