import EventB.Theory.Validate

namespace EventB.Theory.ValidateDemo

open EventB
open EventB.Formula
open EventB.Typing
open EventB.Theory
open EventB.Theory.Validate

private def validDefinition : Declaration :=
  .definitionDecl
    { name := "zero", parameters := [], result := .int, body := .num 0 }

private def invalidDefinition : Declaration :=
  .definitionDecl
    { name := "bad", parameters := [], result := .bool, body := .num 0 }

private def validInference : Declaration :=
  .ruleDecl
    { name := "lt_identity", kind := .inference, parameters := [("x", .int), ("y", .int)]
      premises := [.bin "<" (.id "x") (.id "y")]
      conclusion := some (.bin "<" (.id "x") (.id "y")) }

private def validTheorem : Declaration :=
  .ruleDecl
    { name := "zero_eq", kind := .theorem
      conclusion := some (.bin "=" (.num 0) (.num 0)) }

private def nonDecreasingRewrite : Declaration :=
  .ruleDecl
    { name := "cycle", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.id "x")
      rhs := some (.bin "+" (.id "x") (.num 0)) }

private def validRewrite : Declaration :=
  .ruleDecl
    { name := "add_zero", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.bin "+" (.id "x") (.num 0))
      rhs := some (.id "x") }

#guard Report.isValid (validateDeclaration Theory.empty [] validDefinition)
#guard !Report.isValid (validateDeclaration Theory.empty [] invalidDefinition)
#guard Report.isValid (validateDeclaration Theory.empty [] validInference)
#guard Report.isValid (validateDeclaration Theory.empty [] validTheorem)
#guard Report.isValid (validateDeclaration Theory.empty [] validRewrite)
#guard !Report.isValid (validateDeclaration Theory.empty [] nonDecreasingRewrite)
#guard (validateDeclaration Theory.empty [] nonDecreasingRewrite).issues.any
  (fun issue => issue.field == "orientation")

private def duplicateSpec : Spec :=
  { name := "Duplicate"
    declarations := [validDefinition, validDefinition] }

#guard !Report.isValid (validateSpec Theory.empty duplicateSpec)

end EventB.Theory.ValidateDemo
