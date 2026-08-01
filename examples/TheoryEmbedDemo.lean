/- Checked native theory declarations become Lean expressions with explicit denotations. -/
import EventB.Theory.Embed

namespace EventB.TheoryEmbedDemo

open Lean Elab Command Meta
open EventB EventB.Embedding EventB.Formula EventB.Theory

inductive Colour where
  | red
  | blue

private meta def succeeds (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    pure true
  catch _ => pure false

private meta def checkDefinition : TermElabM Unit := do
  let definition : Definition :=
    { name := "increment", parameters := [("x", .int)], result := .int
      body := .bin "+" (.id "x") (.num 1) }
  let translated ← Embed.translateDefinition {} definition
  let actual ← inferType translated.value
  let expected ← mkArrow (mkConst ``Int) (mkConst ``Int)
  unless ← isDefEq actual expected do
    throwError "definition did not become an Int → Int Lean term"

private meta def checkDatatype : TermElabM Unit := do
  let datatype : Datatype :=
    { name := "Colour", constructors := [{ name := "red" }, { name := "blue" }] }
  let translated ← Embed.checkDatatype {} datatype (mkConst ``Colour)
    [("red", mkConst ``Colour.red), ("blue", mkConst ``Colour.blue)]
  unless translated.constructors.length == 2 do
    throwError "datatype constructor denotations were not retained"

private meta def checkRules : TermElabM Unit := do
  let rewrite : Rule :=
    { name := "add_zero", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.bin "+" (.id "x") (.num 0)), rhs := some (.id "x") }
  let inference : Rule :=
    { name := "lt_identity", kind := .inference,
      parameters := [("x", .int), ("y", .int)]
      premises := [.bin "<" (.id "x") (.id "y")]
      conclusion := some (.bin "<" (.id "x") (.id "y")) }
  let rewriteValue ← Embed.translateRule {} rewrite
  let inferenceValue ← Embed.translateRule {} inference
  unless (← inferType rewriteValue.value).isSort do
    throwError "rewrite was not translated to a proposition"
  unless (← inferType inferenceValue.value).isSort do
    throwError "inference rule was not translated to a proposition"
  let cyclic : Rule :=
    { name := "cyclic", kind := .rewrite, lhs := some (.id "x"), rhs := some (.id "x") }
  unless !(← succeeds do let _ ← Embed.translateRule {} cyclic) do
    throwError "non-decreasing rewrite was accepted"

syntax (name := eventbTheoryEmbedChecks) "#eventb_theory_embed_checks" : command

@[command_elab eventbTheoryEmbedChecks]
meta def elabTheoryEmbedChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_theory_embed_checks) => liftTermElabM do
      checkDefinition
      checkDatatype
      checkRules
  | _ => throwUnsupportedSyntax

#eventb_theory_embed_checks

end EventB.TheoryEmbedDemo
