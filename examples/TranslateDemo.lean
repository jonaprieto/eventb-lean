/-
Kernel-facing formula translation. This is deliberately small: it exercises the
same parser and Meta API that a POG or editor integration can call.
-/
import EventB.Formula.Translate

namespace EventB.TranslateDemo

open Lean Elab Command Meta
open EventB

private def parseFormula (source : String) : TermElabM Formula.Term := do
  match Formula.parse source with
  | .ok term => pure term
  | .error reason => throwError s!"formula `{source}` did not parse: {reason}"

private def checkPredicate (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let value ← Embedding.translatePredicate {} term
  let type ← inferType value
  unless ← isDefEq type (mkSort .zero) do
    throwError s!"translated predicate has type {type}"

private def checkIntegerExpression (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let value ← Embedding.translateExpression {} term
  let type ← inferType value.value
  unless ← isDefEq type (mkConst ``Int) do
    throwError s!"translated expression has type {type}, expected Int"

private def checkRejectsUnknown (source : String) : TermElabM Unit := do
  let term ← parseFormula source
  let failed ← try
    let _ ← Embedding.translatePredicate {} term
    pure false
  catch _ => pure true
  unless failed do
    throwError s!"translation unexpectedly accepted `{source}`"

elab "#eventb_translate_checks" : command => liftTermElabM do
  checkIntegerExpression "1 + 2"
  checkPredicate "1 < 2"
  checkPredicate "1 ∈ ℕ"
  checkPredicate "1 ∈ ℕ ∧ 2 ∉ ℕ1"
  checkPredicate "∀x⦂ℤ·x = x"
  checkPredicate "(1 ↦ 2) ∈ ℕ × ℕ"
  checkRejectsUnknown "missing = 0"

#eventb_translate_checks

end EventB.TranslateDemo
