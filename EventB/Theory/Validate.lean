/-
Bounded validation for native theory declarations.

This module checks declaration bodies against the existing Event-B type checker. It
does not elaborate declarations into Lean definitions yet: a declaration may use its
parameters and visible theory symbols, but not another native declaration body.
Rewrite rules are accepted only when their right side is structurally smaller. That
conservative boundary makes the missing termination proof visible instead of treating
an unproved orientation as a theorem.
-/

import EventB.Typing.Check

namespace EventB.Theory.Validate

open EventB.Formula
open EventB.Prelude
open EventB.Typing

inductive Severity where
  | error
  | warning
  deriving BEq, Repr, Inhabited

inductive ObligationKind where
  | declarationType
  | rewriteTermination
  | rewriteSoundness
  | inferenceSoundness
  | theoremSoundness
  | axiomSoundness
  deriving BEq, Repr, Inhabited

inductive ObligationStatus where
  | checked
  | open
  | assumed
  deriving BEq, Repr, Inhabited

structure Obligation where
  declaration : String
  field : String
  kind : ObligationKind
  status : ObligationStatus
  premises : List Term := []
  conclusion : Option Term := none
  deriving BEq, Repr, Inhabited

structure Issue where
  declaration : String
  field : String
  severity : Severity := .error
  message : String
  deriving BEq, Repr, Inhabited

structure Report where
  issues : List Issue := []
  obligations : List Obligation := []
  deriving BEq, Repr, Inhabited

def Report.isValid (report : Report) : Bool :=
  report.issues.all (·.severity != .error)

def Report.errors (report : Report) : List Issue :=
  report.issues.filter (·.severity == .error)

def Report.append (left right : Report) : Report :=
  { issues := left.issues ++ right.issues
    obligations := left.obligations ++ right.obligations }

private def error (declaration field message : String) : Issue :=
  { declaration, field, message }

private def firstDuplicate (seen : List String) : List String → Option String
  | [] => none
  | name :: names =>
      if seen.contains name then some name else firstDuplicate (name :: seen) names

mutual

private def termSize : Term → Nat
  | .id _ | .num _ => 1
  | .bin _ left right => termSize left + termSize right + 1
  | .pre _ term | .post _ term => termSize term + 1
  | .app function argument | .img function argument =>
      termSize function + termSize argument + 1
  | .set terms => termSizeList terms + 1
  | .bind _ pattern body => termSize pattern + termSize body + 1

private def termSizeList : List Term → Nat
  | [] => 0
  | term :: terms => termSize term + termSizeList terms

end

private def parameterIssues (name : String) (parameters : List (String × Ty)) : List Issue :=
  match firstDuplicate [] (parameters.map (·.1)) with
  | some parameter => [error name "parameters" s!"parameter `{parameter}` is repeated"]
  | none => []

private def hasMVar : Ty → Bool
  | .mvar _ => true
  | .pow type => hasMVar type
  | .prod left right => hasMVar left || hasMVar right
  | _ => false

private def typeNames : Ty → List String
  | .given name => [name]
  | .pow type => typeNames type
  | .prod left right => typeNames left ++ typeNames right
  | _ => []

private def visibleTypeNames (theory : Theory.Env) (roots : List String) : List String :=
  let carriers := (Theory.symbolsIn theory roots).filterMap fun (_, symbol) =>
    if symbol.kind == .carrierSet then some symbol.name else none
  let datatypes := (Theory.declarationsIn theory roots).filterMap fun (_, declaration) =>
    match declaration with
    | .dataType datatype => some datatype.name
    | _ => none
  (carriers ++ datatypes).eraseDups

private def typeParameterIssues (name : String) (parameters : List String) : List Issue :=
  let empty := parameters.find? (· == "")
  let duplicate := firstDuplicate [] parameters
  let reserved := parameters.find? (fun parameter =>
    (coreSymbols.find? (·.name == parameter)).isSome)
  match empty with
  | some _ => [error name "typeParameters" "type parameter names cannot be empty"]
  | none => match duplicate with
    | some parameter =>
        [error name "typeParameters" s!"type parameter `{parameter}` is repeated"]
    | none => match reserved with
      | some parameter =>
          [error name "typeParameters"
            s!"type parameter `{parameter}` is reserved by the core prelude"]
      | none => []

private def typeIssues (theory : Theory.Env) (roots : List String)
    (name field : String) (parameters : List String) (types : List (String × Ty)) : List Issue :=
  let allowed := parameters ++ visibleTypeNames theory roots
  types.flatMap fun (_, type) =>
    (typeNames type).eraseDups |>.filterMap fun typeName =>
      if allowed.contains typeName then none
      else some (error name field
        s!"type `{typeName}` is neither a type parameter nor a visible type")

private def unresolvedTypeIssues (name field : String) (types : List (String × Ty)) :
    List Issue :=
  types.flatMap fun (parameter, type) =>
    if hasMVar type then
      [error name field s!"type of `{parameter}` contains an unresolved metavariable"]
    else []

private def unresolvedResultIssue (name field : String) (type : Ty) : List Issue :=
  if hasMVar type then
    [error name field "type contains an unresolved metavariable"]
  else []

private def expressionIssue (theory : Theory.Env) (roots : List String)
    (parameters : List (String × Ty)) (name field : String) (term : Term) :
    List Issue :=
  match inferTermAt theory roots parameters term with
  | .ok _ => []
  | .error message => [error name field s!"not a well-typed expression: {message}"]

private def predicateIssue (theory : Theory.Env) (roots : List String)
    (parameters : List (String × Ty)) (name field : String) (term : Term) : List Issue :=
  match (checkPred term).run
      { env := parameters, theory, theoryRoots := roots } with
  | .ok _ => []
  | .error message => [error name field s!"not a well-formed predicate: {message}"]

private def definitionIssues (theory : Theory.Env) (roots : List String)
    (definition : Definition) : List Issue :=
  let typeParameterErrors := typeParameterIssues definition.name definition.typeParameters
  let parameterErrors := parameterIssues definition.name definition.parameters
  let parameterTypeErrors := unresolvedTypeIssues definition.name "parameters"
    definition.parameters
  let resultTypeErrors := unresolvedResultIssue definition.name "result" definition.result
  let typeErrors := typeIssues theory roots definition.name "types" definition.typeParameters
    (definition.parameters ++ [("result", definition.result)])
  let bodyErrors := expressionIssue theory roots definition.parameters definition.name "body"
    definition.body
  let resultErrors := match inferTermAt theory roots definition.parameters definition.body with
    | .error _ => []
    | .ok actual =>
        if actual == definition.result then []
        else [error definition.name "result"
          s!"body has type {actual.print}, expected {definition.result.print}"]
  typeParameterErrors ++ parameterErrors ++ parameterTypeErrors ++ resultTypeErrors ++
    typeErrors ++ bodyErrors ++ resultErrors

private def rewriteIssues (theory : Theory.Env) (roots : List String)
    (rule : Rule) : List Issue :=
  let typeParameterErrors := typeParameterIssues rule.name rule.typeParameters
  let parameterErrors := parameterIssues rule.name rule.parameters
  let parameterTypeErrors := unresolvedTypeIssues rule.name "parameters" rule.parameters
  let typeErrors := typeIssues theory roots rule.name "types" rule.typeParameters rule.parameters
  let missing :=
    (if rule.lhs.isNone then [error rule.name "lhs" "rewrite rule needs a left side"] else []) ++
    (if rule.rhs.isNone then [error rule.name "rhs" "rewrite rule needs a right side"] else [])
  match rule.lhs, rule.rhs with
  | some lhs, some rhs =>
      let lhsErrors := expressionIssue theory roots rule.parameters rule.name "lhs" lhs
      let rhsErrors := expressionIssue theory roots rule.parameters rule.name "rhs" rhs
      let rewriteTypeErrors := match inferTermAt theory roots rule.parameters lhs,
          inferTermAt theory roots rule.parameters rhs with
        | .ok left, .ok right =>
            if left == right then []
            else [error rule.name "rhs"
              s!"rewrite changes type from {left.print} to {right.print}"]
        | _, _ => []
      let orientationErrors :=
        if termSize rhs < termSize lhs then []
        else [error rule.name "orientation"
          ("termination is not established: the right side must be structurally smaller; " ++
            "cyclic or precedence-based rewrite systems need a termination certificate")]
      typeParameterErrors ++ parameterErrors ++ parameterTypeErrors ++ typeErrors ++
        lhsErrors ++ rhsErrors ++ rewriteTypeErrors ++
        orientationErrors
  | _, _ => typeParameterErrors ++ parameterErrors ++ parameterTypeErrors ++ typeErrors ++ missing

private def inferenceIssues (theory : Theory.Env) (roots : List String)
    (rule : Rule) : List Issue :=
  let typeParameterErrors := typeParameterIssues rule.name rule.typeParameters
  let parameterErrors := parameterIssues rule.name rule.parameters
  let parameterTypeErrors := unresolvedTypeIssues rule.name "parameters" rule.parameters
  let typeErrors := typeIssues theory roots rule.name "types" rule.typeParameters rule.parameters
  let premiseErrors := rule.premises.flatMap (predicateIssue theory roots rule.parameters
    rule.name "premise")
  let conclusionErrors := match rule.conclusion with
    | some conclusion =>
        predicateIssue theory roots rule.parameters rule.name "conclusion" conclusion
    | none => [error rule.name "conclusion" "inference rule needs a conclusion"]
  typeParameterErrors ++ parameterErrors ++ parameterTypeErrors ++ typeErrors ++ premiseErrors ++
    conclusionErrors

private def theoremIssues (theory : Theory.Env) (roots : List String)
    (rule : Rule) : List Issue :=
  let typeParameterErrors := typeParameterIssues rule.name rule.typeParameters
  let parameterErrors := parameterIssues rule.name rule.parameters
  let parameterTypeErrors := unresolvedTypeIssues rule.name "parameters" rule.parameters
  let typeErrors := typeIssues theory roots rule.name "types" rule.typeParameters rule.parameters
  let premiseErrors := rule.premises.flatMap (predicateIssue theory roots rule.parameters
    rule.name "premise")
  let conclusionErrors := match rule.conclusion with
    | some conclusion =>
        predicateIssue theory roots rule.parameters rule.name "conclusion" conclusion
    | none => [error rule.name "conclusion" "theorem needs a conclusion"]
  typeParameterErrors ++ parameterErrors ++ parameterTypeErrors ++ typeErrors ++ premiseErrors ++
    conclusionErrors

private def datatypeIssues (theory : Theory.Env) (roots : List String)
    (datatype : Datatype) : List Issue :=
  let names := datatype.constructors.map (·.name)
  let duplicate := firstDuplicate [] names
  let duplicateErrors := match duplicate with
    | some name => [error datatype.name "constructors" s!"constructor `{name}` is repeated"]
    | none => []
  let emptyError :=
    if datatype.constructors.isEmpty then
      [error datatype.name "constructors" "datatype needs a constructor"]
    else []
  let typeParameterErrors := typeParameterIssues datatype.name datatype.parameters
  let constructorTypes := datatype.constructors.flatMap fun constructor =>
    constructor.arguments.map (constructor.name, ·)
  let typeErrors := typeIssues theory roots datatype.name "constructors" datatype.parameters
    constructorTypes
  let constructorTypeErrors := datatype.constructors.flatMap fun constructor =>
    unresolvedTypeIssues datatype.name ("constructor " ++ constructor.name) <|
      constructor.arguments.map (fun type => (constructor.name, type))
  duplicateErrors ++ emptyError ++ typeParameterErrors ++ typeErrors ++
    constructorTypeErrors

private def declarationObligations : Declaration → List Obligation
  | .dataType datatype =>
      [{ declaration := datatype.name, field := "declaration", kind := .declarationType
         status := .checked }]
  | .definitionDecl definition =>
      let typeCheck :=
        { declaration := definition.name, field := "type", kind := .declarationType
          status := .checked }
      match definition.kind with
      | .definitional => [typeCheck]
      | .axiomatic =>
          [typeCheck,
            { declaration := definition.name, field := "definition", kind := .axiomSoundness
              status := .assumed }]
  | .ruleDecl rule =>
      match rule.kind with
      | .rewrite =>
          let equation := match rule.lhs, rule.rhs with
            | some lhs, some rhs => some (.bin "=" lhs rhs)
            | _, _ => none
          let termination := match rule.lhs, rule.rhs with
            | some lhs, some rhs =>
                if termSize rhs < termSize lhs then .checked else .open
            | _, _ => .open
          [{ declaration := rule.name, field := "termination", kind := .rewriteTermination
             status := termination },
            { declaration := rule.name, field := "equation", kind := .rewriteSoundness
              status := .open, conclusion := equation }]
      | .inference =>
          [{ declaration := rule.name, field := "rule", kind := .inferenceSoundness
             status := .open, premises := rule.premises, conclusion := rule.conclusion }]
      | .theorem =>
          [{ declaration := rule.name, field := "theorem", kind := .theoremSoundness
             status := .open, premises := rule.premises, conclusion := rule.conclusion }]
      | _ => []

def declaration (theory : Theory.Env) (roots : List String) : Declaration → Report
  | .dataType datatype =>
      { issues := datatypeIssues theory roots datatype
        obligations := declarationObligations (.dataType datatype) }
  | .definitionDecl definition =>
      { issues := definitionIssues theory roots definition
        obligations := declarationObligations (.definitionDecl definition) }
  | .ruleDecl rule =>
      { issues := match rule.kind with
          | .rewrite => rewriteIssues theory roots rule
          | .inference => inferenceIssues theory roots rule
          | .theorem => theoremIssues theory roots rule
          | _ => [error rule.name "kind" "declaration kind is not a supported rule"]
        obligations := declarationObligations (.ruleDecl rule) }

private def declarationParts : Declaration → List String
  | .dataType datatype => datatype.name :: datatype.constructors.map (·.name)
  | .definitionDecl definition => [definition.name]
  | .ruleDecl rule => [rule.name]

private def specNames (spec : Spec) : List String :=
  spec.symbols.map (·.name) ++ spec.declarations.flatMap declarationParts

private def specNameIssues (spec : Spec) : List Issue :=
  match firstDuplicate [] (specNames spec) with
  | some name => [error spec.name "names" s!"name `{name}` is declared more than once"]
  | none => []

private def registrationIssues (env : Theory.Env) (spec : Spec) : List Issue :=
  match Theory.add env spec with
  | .ok _ => []
  | .error message => [error spec.name "registration" message]

def validateDeclaration (theory : Theory.Env) (roots : List String)
    (value : Declaration) : Report :=
  declaration theory roots value

def validateSpec (env : Theory.Env) (spec : Spec) : Report :=
  let registrationErrors := registrationIssues env spec
  let checkingEnv := match Theory.add env spec with
    | .ok extended => extended
    | .error _ => env
  let roots := spec.name :: spec.imports
  let declarationReport : Report := spec.declarations.foldl
    (fun report value => Report.append report (declaration checkingEnv roots value)) {}
  { issues := specNameIssues spec ++ registrationErrors ++ declarationReport.issues
    obligations := declarationReport.obligations }

#guard Report.isValid (validateDeclaration Theory.empty []
  (.definitionDecl
    { name := "zero", parameters := [], result := .int, body := .num 0 }))
#guard Report.isValid (validateDeclaration Theory.empty []
  (.definitionDecl
    { name := "increment", parameters := [("x", .int)], result := .int
      body := .bin "+" (.id "x") (.num 1) }))
#guard !Report.isValid (validateDeclaration Theory.empty []
  (.definitionDecl
    { name := "bad", parameters := [], result := .bool, body := .num 0 }))
#guard Report.isValid (validateDeclaration Theory.empty []
  (.ruleDecl
    { name := "add_zero", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.bin "+" (.id "x") (.num 0))
      rhs := some (.id "x") }))
#guard Report.isValid (validateDeclaration Theory.empty []
  (.ruleDecl
    { name := "lt_identity", kind := .inference, parameters := [("x", .int), ("y", .int)]
      premises := [.bin "<" (.id "x") (.id "y")]
      conclusion := some (.bin "<" (.id "x") (.id "y")) }))
#guard Report.isValid (validateDeclaration Theory.empty []
  (.ruleDecl
    { name := "zero_eq", kind := .theorem
      conclusion := some (.bin "=" (.num 0) (.num 0)) }))
#guard !Report.isValid (validateDeclaration Theory.empty []
  (.ruleDecl
    { name := "cycle", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.id "x")
      rhs := some (.bin "+" (.id "x") (.num 0)) }))
#guard (validateDeclaration Theory.empty []
  (.ruleDecl
    { name := "cycle", kind := .rewrite, parameters := [("x", .int)]
      lhs := some (.id "x")
      rhs := some (.bin "+" (.id "x") (.num 0)) })).issues.any
  (fun issue => issue.field == "orientation")

private def scopedSpec : Spec :=
  { name := "Bounds"
    symbols := [Symbol.mk "LIMIT" .constant (some .int) "A visible theory constant." none []
      (SymbolId.unqualified "LIMIT") SourceRange.synthetic]
    declarations := [.definitionDecl
      { name := "limit_value", result := .int, body := .id "LIMIT" }] }

#guard Report.isValid (validateSpec Theory.empty scopedSpec)

end EventB.Theory.Validate
