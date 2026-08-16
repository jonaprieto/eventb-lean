/-
Kernel-facing formula translation. This is deliberately small: it exercises the
same parser and Meta API that a POG or editor integration can call.
-/
import EventB.Formula.Translate

namespace EventB.TranslateDemo

open Lean Elab Command Meta
open EventB

#guard match Formula.parse "{1 ↦ 2}" with
  | .ok (.set [.bin "↦" (.num 1) (.num 2)]) => true
  | _ => false

private meta def parseFormula (source : String) : TermElabM Formula.Term := do
  match Formula.parse source with
  | .ok term => pure term
  | .error reason => throwError s!"formula `{source}` did not parse: {reason}"

private meta def checkPredicate (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let value ← Embedding.translatePredicate {} term
  let type ← inferType value
  unless ← isDefEq type (mkSort .zero) do
    throwError s!"translated predicate has type {type}"

private meta def checkIntegerExpression (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let value ← Embedding.translateExpression {} term
  let type ← inferType value.value
  unless ← isDefEq type (mkConst ``Int) do
    throwError s!"translated expression has type {type}, expected Int"

private meta def checkRejectsUnknown (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let failed ← try
    let _ ← Embedding.translatePredicate {} term
    pure false
  catch _ => pure true
  unless failed do
    throwError s!"translation unexpectedly accepted `{source}`"

private meta def checkRejectsWrongBinding : TermElabM Unit := do
  let term ← parseFormula "x = x"
  let theory : Theory.Env :=
    { theories := [Theory.core,
        { name := "T", symbols :=
            [EventB.Prelude.Symbol.mk "x" .constant (some .int) "" none []
              (EventB.Prelude.SymbolId.unqualified "x") EventB.SourceRange.synthetic] }] }
  let context : Embedding.KernelContext :=
    { theory, roots := ["T"], bindings :=
        [{ name := "x", ty := .bool, value := mkConst ``Bool.true }] }
  let failed ← try
    let _ ← Embedding.translatePredicate context term
    pure false
  catch _ => pure true
  unless failed do
    throwError "translation accepted a binding with the wrong Event-B type"

private meta def checkSemanticFunction : TermElabM Unit := do
  let setType ← mkArrow (mkConst ``Int) (mkSort .zero)
  let value ← withLocalDeclD `set setType fun set => do
    mkLambdaFVars #[set] (mkApp (mkConst ``Int.ofNat) (mkNatLit 0))
  let context : Embedding.KernelContext :=
    { functions :=
        [{ name := "card", argument := .pow .int, result := .int, value }] }
  let term ← parseFormula "card(∅) = 0"
  let _ ← Embedding.translatePredicate context term

private meta def checkLambda : TermElabM Unit := do
  let relationType ← mkArrow (← mkAppM ``Prod #[mkConst ``Int, mkConst ``Int]) (mkSort .zero)
  withLocalDeclD `relation relationType fun relation => do
    let context : Embedding.KernelContext :=
      { bindings :=
          [{ name := "r", ty := .pow (.prod .int .int), value := relation }] }
    for source in ["r = λx⦂ℤ·x ↦ x", "r = λx·x ↦ x"] do
      let term ← parseFormula source
      let _ ← Embedding.translatePredicate context term

private meta def checkRelationSubtraction : MetaM Unit := do
  let intType := mkConst ``Int
  let prop := mkSort .zero
  let setType ← mkArrow intType prop
  let pairType ← mkAppM ``Prod #[intType, intType]
  let relationType ← mkArrow pairType prop
  withLocalDeclD `set setType fun set =>
    withLocalDeclD `relation relationType fun relation => do
      let context : Embedding.KernelContext :=
        { bindings :=
            [{ name := "S", ty := .pow .int, value := set }
            , { name := "r", ty := .pow (.prod .int .int), value := relation }] }
      let some restrictionTerm := (Formula.parse "S ◁ r").toOption |
        throwError "restriction did not parse"
      let some subtractionTerm := (Formula.parse "S ⩤ r").toOption | throwError
        "subtraction did not parse"
      let restriction ← Embedding.translateExpression context restrictionTerm
      let subtraction ← Embedding.translateExpression context subtractionTerm
      unless !(← isDefEq restriction.value subtraction.value) do
        throwError "relation subtraction translated as domain restriction"

syntax (name := eventbTranslateChecks) "#eventb_translate_checks" : command

@[command_elab eventbTranslateChecks]
meta def elabTranslateChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_translate_checks) => liftTermElabM do
      checkIntegerExpression "1 + 2"
      checkIntegerExpression "2 ^ 3"
      checkPredicate "1 < 2"
      checkPredicate "bool(1 < 2) = TRUE"
      checkPredicate "1 ∈ ℕ"
      checkPredicate "1 ∈ ℕ ∧ 2 ∉ ℕ1"
      checkPredicate "1 ∈ {1, 2}"
      checkPredicate "∅ ⊆ ℕ"
      checkPredicate "1 ∈ dom({1 ↦ 2})"
      checkPredicate "2 ∈ ran({1 ↦ 2})"
      checkPredicate "1 ∈ dom(ℕ ◁ {1 ↦ 2})"
      checkPredicate "1 ∈ dom({1 ↦ 2} ; {2 ↦ 3})"
      checkPredicate "1 ∈ dom({1 ↦ 2}  {1 ↦ 3})"
      checkPredicate "1 ∈ dom({1 ↦ 2} ⊗ {1 ↦ 3})"
      checkPredicate "∀x⦂ℤ·x = x"
      checkPredicate "(1 ↦ 2) ∈ ℕ × ℕ"
      checkPredicate "{1 ↦ 2} ∈ (ℕ → ℕ)"
      checkPredicate "{1} ∈ ℙ1(ℕ)"
      checkPredicate "{x⦂ℤ · x < 3 ∣ x} = {0, 1, 2}"
      checkRejectsUnknown "missing = 0"
      checkRejectsWrongBinding
      checkSemanticFunction
      checkLambda
      liftMetaM checkRelationSubtraction
  | _ => throwUnsupportedSyntax

#eventb_translate_checks

end EventB.TranslateDemo
