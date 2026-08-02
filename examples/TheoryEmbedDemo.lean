/- Checked native theory declarations become Lean expressions with explicit denotations. -/
import EventB.Theory.Embed
import EventB.Trust.Replay

namespace EventB.TheoryEmbedDemo

open Lean Elab Command Meta
open EventB EventB.Embedding EventB.Formula EventB.Theory

theorem zeroReflexive (zero : Int) : zero = zero := rfl

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
  let identity : Definition :=
    { name := "identity", typeParameters := ["α"]
      parameters := [("x", .given "α")], result := .given "α", body := .id "x" }
  let context : KernelContext :=
    { signature := { carriers := [("α", mkConst ``Int)] } }
  let translated ← Embed.translateDefinition context identity
  unless ← isDefEq (← inferType translated.value) expected do
    throwError "polymorphic definition was not instantiated at Int"
  unless !(← succeeds do let _ ← Embed.translateDefinition {} identity) do
    throwError "a polymorphic definition was accepted without an instantiation"

private meta def checkResolvedDefinitions : TermElabM Unit := do
  let theory ← match Theory.add Theory.empty
      { name := "Resolved", declarations :=
        [.definitionDecl
          { name := "zero", result := .int, body := .num 0 },
         .definitionDecl
          { name := "one", result := .int, body := .bin "+" (.id "zero") (.num 1) },
         .definitionDecl
          { name := "increment", parameters := [("x", .int)], result := .int,
            body := .bin "+" (.id "x") (.num 1) }] } with
    | .ok value => pure value
    | .error error => throwError error
  let context ← Embed.translateDefinitions
    { theory, roots := ["Resolved"] }
  let equality ← match Formula.parse "one = 1 ∧ increment(1) = 2" with
    | .ok value => pure value
    | .error error => throwError error
  let _ ← Embedding.translatePredicate context equality

private meta def checkDatatype : TermElabM Unit := do
  let datatype : Datatype :=
    { name := "Colour", constructors := [{ name := "red" }, { name := "blue" }] }
  let translated ← Embed.checkDatatype {} datatype (mkConst ``Colour)
    [("red", mkConst ``Colour.red), ("blue", mkConst ``Colour.blue)]
  unless translated.constructors.length == 2 do
    throwError "datatype constructor denotations were not retained"
  unless !(← succeeds do
      let _ ← Embed.checkDatatype {} datatype (mkConst ``Bool.true)
        [("red", mkConst ``Colour.red), ("blue", mkConst ``Colour.blue)]) do
    throwError "a proposition value was accepted as a datatype type"

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
  let identity : Rule :=
    { name := "identity_eq", kind := .theorem, typeParameters := ["α"]
      parameters := [("x", .given "α")]
      conclusion := some (.bin "=" (.id "x") (.id "x")) }
  let context : KernelContext :=
    { signature := { carriers := [("α", mkConst ``Int)] } }
  let identityValue ← Embed.translateRule context identity
  unless (← inferType identityValue.value).isSort do
    throwError "polymorphic theorem was not translated to a proposition"
  let cyclic : Rule :=
    { name := "cyclic", kind := .rewrite, lhs := some (.id "x"), rhs := some (.id "x") }
  unless !(← succeeds do let _ ← Embed.translateRule {} cyclic) do
    throwError "non-decreasing rewrite was accepted"

private meta def checkKernelReplay : TermElabM Unit := do
  let theory ← match Theory.add Theory.empty
      { name := "ReplayTheory", declarations :=
        [.definitionDecl { name := "zero", result := .int, body := .num 0 }] } with
    | .ok value => pure value
    | .error error => throwError error
  let context ← Embed.translateDefinitions { theory, roots := ["ReplayTheory"] }
  let obligation : POG.Obligation :=
    { component := "ReplayTheory", name := "zero/reflexive/THM", kind := "THM"
      goal := some (.bin "=" (.id "zero") (.id "zero")) }
  let report ← Trust.Replay.validate context obligation
    (.kernel "EventB.TheoryEmbedDemo.zeroReflexive" [])
  unless report.replayed do
    throwError "theory-resolved kernel evidence was not replayed"

syntax (name := eventbTheoryEmbedChecks) "#eventb_theory_embed_checks" : command

@[command_elab eventbTheoryEmbedChecks]
meta def elabTheoryEmbedChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_theory_embed_checks) => liftTermElabM do
      checkDefinition
      checkResolvedDefinitions
      checkDatatype
      checkRules
      checkKernelReplay
  | _ => throwUnsupportedSyntax

#eventb_theory_embed_checks

end EventB.TheoryEmbedDemo
