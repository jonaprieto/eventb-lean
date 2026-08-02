/-
Kernel-facing theory declarations.

Native theory validation remains syntax-level.  This module turns checked
definitions and rules into Lean expressions, while datatypes receive explicit
Lean type and constructor denotations.  No declaration is silently promoted to
an axiom: axiomatic definitions keep their kind in the returned descriptor.
-/

import EventB.Formula.Translate
import EventB.Theory.Validate

namespace EventB.Theory.Embed

open Lean Meta
open EventB EventB.Embedding EventB.Formula EventB.Prelude EventB.Typing

structure KernelDefinition where
  name : String
  kind : DefinitionKind
  result : Ty
  value : Expr
  deriving Repr

structure KernelConstructor where
  name : String
  value : Expr
  deriving Repr

structure KernelDatatype where
  name : String
  value : Expr
  constructors : List KernelConstructor
  deriving Repr

structure KernelRule where
  name : String
  kind : DeclarationKind
  value : Expr
  /-- Validation obligations remain open until separate proof evidence is attached. -/
  obligations : List Validate.Obligation := []
  deriving Repr

private def reportText (report : Validate.Report) : String :=
  String.intercalate "; " (report.errors.map (·.message))

private def requireValid (env : Theory.Env) (roots : List String)
    (declaration : Declaration) : MetaM Unit := do
  let report := Validate.validateDeclaration env roots declaration
  unless report.isValid do
    throwError s!"invalid theory declaration: {reportText report}"

private def checkTypeParameters (context : KernelContext) (parameters : List String) :
    MetaM Unit := do
  for parameter in parameters do
    match context.signature.carriers.find? (·.1 == parameter) with
    | none =>
        throwError s!"polymorphic type parameter `{parameter}` has no Lean instantiation"
    | some (_, value) =>
        unless (← inferType value).isSort do
          throwError s!"Lean instantiation for type parameter `{parameter}` is not a type"

private def withParameters {α : Type} (context : KernelContext)
    (parameters : List (String × Ty))
    (continuation : KernelContext → List Expr → MetaM α) : MetaM α :=
  match parameters with
  | [] => continuation context []
  | (name, ty) :: rest => do
      withLocalDeclD (Name.mkSimple name) (← leanType context ty) fun value => do
        let context := { context with bindings :=
          { name, ty, value } :: context.bindings }
        withParameters context rest fun context values =>
          continuation context (value :: values)

private def functionType (context : KernelContext) (parameters : List (String × Ty))
    (result : Ty) : MetaM Expr := do
  let result ← leanType context result
  parameters.foldrM (fun (_, ty) result => do
    let type ← leanType context ty
    mkArrow type result) result

private def checkedFunction (context : KernelContext) (parameters : List (String × Ty))
    (result : Ty) (value : Expr) : MetaM Unit := do
  let expected ← functionType context parameters result
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError s!"translated declaration has type {actual}, expected {expected}"

def translateDefinition (context : KernelContext) (definition : Definition) :
    MetaM KernelDefinition := do
  requireValid context.theory context.roots (.definitionDecl definition)
  checkTypeParameters context definition.typeParameters
  withParameters context definition.parameters fun bodyContext parameters => do
    let body ← translateExpression bodyContext definition.body
    unless body.ty == definition.result do
      throwError s!"definition `{definition.name}` has body type {body.ty.print}, " ++
        s!"expected {definition.result.print}"
    let value ← mkLambdaFVars parameters.toArray body.value
    checkedFunction context definition.parameters definition.result value
    pure { name := definition.name, kind := definition.kind, result := definition.result, value }

private def productType : List Ty → Option Ty
  | [] => none
  | type :: types => some (types.foldl (fun result next => .prod result next) type)

private def productValues (value : Expr) : Nat → MetaM (List Expr)
  | 0 => pure []
  | 1 => pure [value]
  | count + 1 => do
      let left ← mkAppM ``Prod.fst #[value]
      let right ← mkAppM ``Prod.snd #[value]
      return (← productValues left count) ++ [right]

private def uncurried (context : KernelContext) (parameters : List (String × Ty))
    (value : Expr) : MetaM Expr := do
  let some argumentType := productType (parameters.map (·.2)) | unreachable!
  withLocalDeclD `arguments (← leanType context argumentType) fun arguments => do
    let values ← productValues arguments parameters.length
    let applied := values.foldl (fun function argument => mkApp function argument) value
    mkLambdaFVars #[arguments] applied

private def addDefinitionBinding (context : KernelContext) (definition : Definition)
    (translated : KernelDefinition) : MetaM KernelContext :=
  match definition.parameters with
  | [] =>
      pure { context with bindings :=
        { name := definition.name, ty := definition.result, value := translated.value } ::
          context.bindings }
  | [(_, argument)] =>
      pure { context with functions :=
        { name := definition.name, argument, result := definition.result,
          value := translated.value } :: context.functions }
  | parameters =>
      match productType (parameters.map (·.2)) with
      | none => throwError s!"definition `{definition.name}` has no parameters"
      | some argument => do
          let value ← uncurried context parameters translated.value
          pure { context with functions :=
            { name := definition.name, argument, result := definition.result, value } ::
              context.functions }

/-- Translate all visible definitional declarations and add their Lean denotations to the
formula context. Declarations are resolved in theory order, so a definition may depend on
an earlier definition while still requiring explicit model and datatype denotations. -/
def translateDefinitions (context : KernelContext) : MetaM KernelContext := do
  let mut resolved := context
  for (_, definition) in Theory.definitionsIn context.theory context.roots do
    let translated ← translateDefinition resolved definition
    resolved ← addDefinitionBinding resolved definition translated
  pure resolved

private def constructorType (context : KernelContext) (arguments : List Ty) (result : Expr) :
    MetaM Expr := do
  arguments.foldrM (fun type result => do
    let type ← leanType context type
    mkArrow type result) result

private def namedParameters : Nat → List Ty → List (String × Ty)
  | _, [] => []
  | index, type :: types =>
      ("arg" ++ toString index, type) :: namedParameters (index + 1) types

private def checkedUncurriedFunction (context : KernelContext) (name : String)
    (argument result : Ty) (value : Expr) : MetaM Unit := do
  let argumentType ← leanType context argument
  let resultType ← leanType context result
  let actual ← inferType value
  unless ← isDefEq actual (← mkArrow argumentType resultType) do
    throwError s!"constructor `{name}` has Lean type {actual}, " ++
      s!"expected {argumentType} → {resultType}"

def checkDatatype (context : KernelContext) (datatype : Datatype) (value : Expr)
    (constructors : List (String × Expr)) : MetaM KernelDatatype := do
  requireValid context.theory context.roots (.dataType datatype)
  checkTypeParameters context datatype.parameters
  unless (← inferType value).isSort do
    throwError s!"datatype `{datatype.name}` denotation is not a Lean type"
  let expectedNames := datatype.constructors.map (·.name)
  let actualNames := constructors.map (·.1)
  unless expectedNames == actualNames do
    throwError s!"datatype `{datatype.name}` constructors do not match the declaration"
  let checked ← datatype.constructors.zip constructors |>.mapM fun pair => do
    let (declaration, (name, constructor)) := pair
    let expected ← constructorType context declaration.arguments value
    let actual ← inferType constructor
    unless ← isDefEq actual expected do
      throwError s!"constructor `{name}` has type {actual}, expected {expected}"
    pure { name, value := constructor }
  pure { name := datatype.name, value, constructors := checked }

/-- Check datatype denotations and add their constructors to a formula context. -/
def addDatatypeBindings (context : KernelContext) (datatype : Datatype) (value : Expr)
    (constructors : List (String × Expr)) : MetaM KernelContext := do
  let checked ← checkDatatype context datatype value constructors
  let mut resolved := context
  for (declaration, constructor) in datatype.constructors.zip checked.constructors do
    match declaration.arguments with
    | [] =>
        resolved := { resolved with bindings :=
          { name := constructor.name, ty := .given datatype.name, value := constructor.value } ::
            resolved.bindings }
    | [argument] =>
        resolved := { resolved with functions :=
          { name := constructor.name, argument, result := .given datatype.name,
            value := constructor.value } :: resolved.functions }
    | arguments =>
        match productType arguments with
        | none => throwError s!"constructor `{constructor.name}` has no arguments"
        | some argument => do
            let parameters := namedParameters 0 arguments
            let function ← uncurried context parameters constructor.value
            checkedUncurriedFunction context constructor.name argument
              (.given datatype.name) function
            resolved := { resolved with functions :=
              { name := constructor.name, argument, result := .given datatype.name,
                value := function } :: resolved.functions }
  pure resolved

private def implications : List Expr → Expr → MetaM Expr
  | [], conclusion => pure conclusion
  | premise :: premises, conclusion => do
      mkArrow premise (← implications premises conclusion)

def translateRule (context : KernelContext) (rule : Rule) : MetaM KernelRule := do
  requireValid context.theory context.roots (.ruleDecl rule)
  checkTypeParameters context rule.typeParameters
  withParameters context rule.parameters fun bodyContext parameters => do
    let proposition ← match rule.kind with
      | .rewrite => do
          let lhs ← translateExpression bodyContext rule.lhs.get!
          let rhs ← translateExpression bodyContext rule.rhs.get!
          unless lhs.ty == rhs.ty do
            throwError s!"rewrite `{rule.name}` changes type from {lhs.ty.print} " ++
              s!"to {rhs.ty.print}"
          mkAppM ``Eq #[lhs.value, rhs.value]
      | .inference | .theorem => do
          let premises ← rule.premises.mapM (translatePredicate bodyContext)
          let conclusion ← translatePredicate bodyContext rule.conclusion.get!
          implications premises conclusion
      | _ => throwError s!"unsupported theory rule `{rule.name}`"
    let value ← mkForallFVars parameters.toArray proposition
    let actual ← inferType value
    unless ← isDefEq actual (mkSort .zero) do
      throwError s!"translated rule `{rule.name}` is not a proposition"
    let obligations := (Validate.validateDeclaration context.theory context.roots
      (.ruleDecl rule)).obligations
    pure { name := rule.name, kind := rule.kind, value, obligations }

end EventB.Theory.Embed
