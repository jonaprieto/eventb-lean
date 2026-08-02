/-
The native Event-B theory environment.

The core prelude is always present. User theories will add symbols and imports here;
model components remain a separate layer in the environment.
-/

import EventB.Formula.Parse
import EventB.Prelude

namespace EventB.Theory

open EventB.Prelude

inductive DeclarationKind where
  | datatype
  | definition
  | axiom
  | rewrite
  | inference
  | theorem
  deriving BEq, Repr, Inhabited

inductive DefinitionKind where
  | definitional
  | axiomatic
  deriving BEq, Repr, Inhabited

structure Constructor where
  name : String
  arguments : List Typing.Ty := []
  deriving BEq, Repr, Inhabited

structure Datatype where
  name : String
  parameters : List String := []
  constructors : List Constructor := []
  deriving BEq, Repr, Inhabited

structure Definition where
  name : String
  parameters : List (String × Typing.Ty) := []
  result : Typing.Ty
  body : Formula.Term
  kind : DefinitionKind := .definitional
  /-- Rigid type names used by this declaration, instantiated by the embedding context. -/
  typeParameters : List String := []
  deriving BEq, Repr, Inhabited

structure Rule where
  name : String
  kind : DeclarationKind
  parameters : List (String × Typing.Ty) := []
  premises : List Formula.Term := []
  lhs : Option Formula.Term := none
  rhs : Option Formula.Term := none
  conclusion : Option Formula.Term := none
  /-- Rigid type names used by this rule, instantiated by the embedding context. -/
  typeParameters : List String := []
  deriving BEq, Repr, Inhabited

inductive Declaration where
  | dataType (value : Datatype)
  | definitionDecl (value : Definition)
  | ruleDecl (value : Rule)
  deriving BEq, Repr, Inhabited

def Declaration.name : Declaration → String
  | .dataType value => value.name
  | .definitionDecl value => value.name
  | .ruleDecl value => value.name

def Declaration.kind : Declaration → DeclarationKind
  | .dataType _ => .datatype
  | .definitionDecl value => match value.kind with
    | .definitional => .definition
    | .axiomatic => .axiom
  | .ruleDecl value => value.kind

def Declaration.typeParameters : Declaration → List String
  | .dataType value => value.parameters
  | .definitionDecl value => value.typeParameters
  | .ruleDecl value => value.typeParameters

private def productType : List Typing.Ty → Option Typing.Ty
  | [] => none
  | type :: types => some <| types.foldl (fun result next => .prod result next) type

def Constructor.type (datatype : Datatype) (constructor : Constructor) : Typing.Ty :=
  match productType constructor.arguments with
  | none => .given datatype.name
  | some arguments => .pow (.prod arguments (.given datatype.name))

def Definition.type (value : Definition) : Typing.Ty :=
  match productType (value.parameters.map (·.2)) with
  | none => value.result
  | some arguments => .pow (.prod arguments value.result)

def Declaration.expressionType? : Declaration → Option Typing.Ty
  | .definitionDecl value => some value.type
  | _ => none

structure Spec where
  name : String
  imports : List String := []
  symbols : List Symbol := []
  declarations : List Declaration := []
  deriving Repr, Inhabited

structure Env where
  theories : List Spec := []
  deriving Repr, Inhabited

def core : Spec :=
  { name := "EventB.Core", symbols := coreSymbols }

def empty : Env :=
  { theories := [core] }

def canonicalize (theory : Spec) : Spec :=
  { theory with symbols := theory.symbols.map fun symbol =>
      { symbol with id := SymbolId.qualified theory.name symbol.name } }

def declarationId (theory : String) (declaration : Declaration) : SymbolId :=
  SymbolId.qualified theory declaration.name

def lookupTheory? (env : Env) (name : String) : Option Spec :=
  env.theories.find? (·.name == name)

private def firstDuplicate (seen : List String) : List String → Option String
  | [] => none
  | name :: names =>
    if seen.contains name then some name else firstDuplicate (name :: seen) names

private def closureAux (env : Env) : Nat → List String → String → List String
  | 0, seen, _ => seen
  | fuel + 1, seen, name =>
    if seen.contains name then seen
    else
      match lookupTheory? env name with
      | none => name :: seen
      | some theory =>
        let seen := theory.imports.foldl
          (fun seen imported => closureAux env fuel seen imported) seen
        name :: seen

private def visibleTheoryNames (env : Env) (roots : List String) : List String :=
  let fuel := env.theories.length + roots.length + 1
  let names := roots.foldl (fun seen root => closureAux env fuel seen root) []
  (core.name :: names).eraseDups

def lookupIn? (env : Env) (roots : List String) (name : String) : Option (String × Symbol) :=
  visibleTheoryNames env roots |>.findSome? fun theoryName => do
    let theory ← lookupTheory? env theoryName
    let symbol ← theory.symbols.find? (fun symbol => symbol.name == name)
    return (theory.name, symbol)

def symbolsIn (env : Env) (roots : List String) : List (String × Symbol) :=
  visibleTheoryNames env roots |>.flatMap fun theoryName =>
    match lookupTheory? env theoryName with
    | none => []
    | some theory => theory.symbols.map (theory.name, ·)

def declarationsIn (env : Env) (roots : List String) : List (String × Declaration) :=
  visibleTheoryNames env roots |>.flatMap fun theoryName =>
    match lookupTheory? env theoryName with
    | none => []
    | some theory => theory.declarations.map (theory.name, ·)

def namesWithApplication (env : Env) (roots : List String) (application : ApplicationKind) :
    List String :=
  let symbols := (symbolsIn env roots).filterMap fun (_, symbol) =>
    if symbol.application == some application then some symbol.name else none
  let definitions := if application == .total then
      (declarationsIn env roots).filterMap fun (_, declaration) =>
        match declaration with
        | .definitionDecl value => some value.name
        | _ => none
    else []
  (symbols ++ definitions).eraseDups

def definedness? (env : Env) (roots : List String) (name : String) : List Definedness :=
  (lookupIn? env roots name).map (·.2.definedness) |>.getD []

def declaration? (env : Env) (roots : List String) (name : String) :
    Option (String × Declaration) :=
  declarationsIn env roots |>.find? (·.2.name == name)

def constructor? (env : Env) (roots : List String) (name : String) :
    Option (String × Datatype × Constructor) :=
  declarationsIn env roots |>.findSome? fun (owner, declaration) =>
    match declaration with
    | .dataType datatype => datatype.constructors.find? (·.name == name) |>.map
        (owner, datatype, ·)
    | _ => none

def isDeclarationIn (env : Env) (roots : List String) (name : String) : Bool :=
  (declaration? env roots name).isSome

def definitionsIn (env : Env) (roots : List String) : List (String × Definition) :=
  declarationsIn env roots |>.filterMap fun (owner, declaration) =>
    match declaration with
    | .definitionDecl value => some (owner, value)
    | _ => none

def rewriteRulesIn (env : Env) (roots : List String) : List (String × Rule) :=
  declarationsIn env roots |>.filterMap fun (owner, declaration) =>
    match declaration with
    | .ruleDecl value => if value.kind == .rewrite then some (owner, value) else none
    | _ => none

private def termSize : Formula.Term → Nat
  | .id _ | .num _ => 1
  | .bin _ left right => termSize left + termSize right + 1
  | .pre _ term | .post _ term => termSize term + 1
  | .app function argument | .img function argument =>
      termSize function + termSize argument + 1
  | .set terms => terms.foldl (fun size term => size + termSize term) 1
  | .bind _ pattern body => termSize pattern + termSize body + 1

private def patternShape : Formula.Term → Formula.Term → Bool
  | .id _, .id _ => true
  | .bin leftOp leftA leftB, .bin rightOp rightA rightB =>
      leftOp == rightOp && patternShape leftA rightA && patternShape leftB rightB
  | _, _ => false

mutual

private def referencesBound : Nat → List String → Formula.Term → Bool
  | 0, _, _ => false
  | _ + 1, bound, .id name => bound.contains name
  | _ + 1, _, .num _ => false
  | fuel + 1, bound, .bin _ left right =>
      referencesBound fuel bound left || referencesBound fuel bound right
  | fuel + 1, bound, .pre _ term => referencesBound fuel bound term
  | fuel + 1, bound, .post _ term => referencesBound fuel bound term
  | fuel + 1, bound, .app function argument =>
      referencesBound fuel bound function || referencesBound fuel bound argument
  | fuel + 1, bound, .img function argument =>
      referencesBound fuel bound function || referencesBound fuel bound argument
  | fuel + 1, bound, .set terms => referencesBoundList fuel bound terms
  | fuel + 1, bound, .bind _ pattern body =>
      let shadowed := Formula.patternNames pattern
      referencesBound fuel (bound.filter (fun name => !shadowed.contains name)) body

termination_by fuel _ _ => fuel

private def referencesBoundList : Nat → List String → List Formula.Term → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => false
  | fuel + 1, bound, term :: terms =>
      referencesBound fuel bound term || referencesBoundList fuel bound terms

termination_by fuel _ _ => fuel

end

private def matchRewrite : Nat → List String → List (String × String) → List String →
    Formula.Term → Formula.Term → List (String × Formula.Term) →
    Option (List (String × Formula.Term))
  | 0, _, _, _, _, _, _ => none
  | _ + 1, parameters, bound, targetBound, .id name, target, substitutions =>
      match bound.find? (·.1 == name) with
      | some (_, targetName) =>
          match target with
          | .id actual => if actual == targetName then some substitutions else none
          | _ => none
      | none =>
          if parameters.contains name then
            if referencesBound (termSize target + 1) targetBound target then none
            else match substitutions.find? (·.1 == name) with
              | some (_, previous) =>
                  if Formula.alphaEq previous target then some substitutions else none
              | none => some ((name, target) :: substitutions)
          else if Formula.alphaEq (.id name) target then some substitutions else none
  | _, _, _, _, .num left, .num right, substitutions =>
      if left == right then some substitutions else none
  | fuel + 1, parameters, bound, targetBound,
      .bin leftOp leftA leftB, .bin rightOp rightA rightB, substitutions =>
      if leftOp != rightOp then none
      else do
        let substitutions ← matchRewrite fuel parameters bound targetBound
          leftA rightA substitutions
        matchRewrite fuel parameters bound targetBound leftB rightB substitutions
  | fuel + 1, parameters, bound, targetBound, .pre leftOp left, .pre rightOp right,
      substitutions =>
      if leftOp == rightOp then
        matchRewrite fuel parameters bound targetBound left right substitutions
      else none
  | fuel + 1, parameters, bound, targetBound, .post leftOp left, .post rightOp right,
      substitutions =>
      if leftOp == rightOp then
        matchRewrite fuel parameters bound targetBound left right substitutions
      else none
  | fuel + 1, parameters, bound, targetBound,
      .app leftFunction leftArgument, .app rightFunction rightArgument, substitutions => do
      let substitutions ← matchRewrite fuel parameters bound targetBound
        leftFunction rightFunction substitutions
      matchRewrite fuel parameters bound targetBound leftArgument rightArgument substitutions
  | fuel + 1, parameters, bound, targetBound,
      .img leftRelation leftSet, .img rightRelation rightSet, substitutions => do
      let substitutions ← matchRewrite fuel parameters bound targetBound
        leftRelation rightRelation substitutions
      matchRewrite fuel parameters bound targetBound leftSet rightSet substitutions
  | fuel + 1, parameters, bound, targetBound, .set leftTerms, .set rightTerms,
      substitutions =>
      if leftTerms.length != rightTerms.length then none
      else leftTerms.zip rightTerms |>.foldlM
        (fun substitutions (left, right) =>
          matchRewrite fuel parameters bound targetBound left right substitutions) substitutions
  | fuel + 1, parameters, bound, targetBound,
      .bind leftKind leftPattern leftBody, .bind rightKind rightPattern rightBody,
      substitutions =>
      let leftNames := Formula.patternNames leftPattern
      let rightNames := Formula.patternNames rightPattern
      if leftKind != rightKind || !patternShape leftPattern rightPattern ||
          leftNames.length != rightNames.length ||
          leftNames.eraseDups.length != leftNames.length ||
          rightNames.eraseDups.length != rightNames.length then none
      else
        let localBound := leftNames.zip rightNames
        let bound := localBound ++ bound.filter (fun pair => !leftNames.contains pair.1)
        let targetBound := rightNames ++ targetBound.filter (fun name => !rightNames.contains name)
        matchRewrite fuel parameters bound targetBound leftBody rightBody substitutions
  | _, _, _, _, _, _, _ => none
termination_by fuel _ _ _ _ _ _ => fuel

private def rewriteRoot (rules : List (String × Rule)) (term : Formula.Term) :
    Option Formula.Term :=
  rules.findSome? fun (_, rule) => do
    let lhs ← rule.lhs
    let rhs ← rule.rhs
    if termSize rhs >= termSize lhs then none else
      let fuel := termSize lhs + termSize term + 1
      let substitutions ← matchRewrite fuel (rule.parameters.map (·.1)) [] [] lhs term []
      some (Formula.subst substitutions rhs)

private def normalizeAux (rules : List (String × Rule)) : Nat → Formula.Term → Formula.Term
  | 0, term => term
  | fuel + 1, term =>
      match rewriteRoot rules term with
      | some replacement => normalizeAux rules fuel replacement
      | none => match term with
        | .bin op left right => .bin op (normalizeAux rules fuel left)
            (normalizeAux rules fuel right)
        | .pre op value => .pre op (normalizeAux rules fuel value)
        | .post op value => .post op (normalizeAux rules fuel value)
        | .app function argument => .app (normalizeAux rules fuel function)
            (normalizeAux rules fuel argument)
        | .img relation set => .img (normalizeAux rules fuel relation)
            (normalizeAux rules fuel set)
        | .set values => .set (values.map (normalizeAux rules fuel))
        | .bind kind pattern body => .bind kind (normalizeAux rules fuel pattern)
            (normalizeAux rules fuel body)
        | _ => term

def normalize (env : Env) (roots : List String) (term : Formula.Term) : Formula.Term :=
  let rules := rewriteRulesIn env roots
  normalizeAux rules (termSize term * (rules.length + 1) + 1) term

private def declarationNames (declarations : List Declaration) : List String :=
  declarations.map Declaration.name

private def constructorNames (datatype : Datatype) : List String :=
  datatype.constructors.map (·.name)

private def declarationParts (declaration : Declaration) : List String :=
  match declaration with
  | .dataType datatype => datatype.name :: constructorNames datatype
  | .definitionDecl definition => [definition.name]
  | .ruleDecl rule => [rule.name]

private def declarationNamesAll (declarations : List Declaration) : List String :=
  declarations.flatMap declarationParts

private def isDefinitionName (declarations : List Declaration) (name : String) : Bool :=
  declarations.any fun declaration => match declaration with
    | .definitionDecl definition => definition.name == name
    | _ => false

private def duplicateName (names : List String) : Option String := firstDuplicate [] names

private def typeParameterError (name : String) (parameters : List String) : Option String :=
  if parameters.any (· == "") then
    some s!"declaration `{name}` has an empty type parameter"
  else match duplicateName parameters with
    | some parameter => some s!"type parameter `{parameter}` is repeated"
    | none => match coreSymbols.find? (fun symbol => parameters.contains symbol.name) with
        | some symbol => some s!"type parameter `{symbol.name}` is reserved by the core prelude"
        | none => none

private def declarationError (declaration : Declaration) : Option String :=
  match declaration with
  | .dataType datatype =>
      if datatype.constructors.isEmpty then
        some s!"datatype `{datatype.name}` needs a constructor"
      else match typeParameterError datatype.name datatype.parameters with
        | some error => some error
        | none => match duplicateName (datatype.parameters ++ constructorNames datatype) with
            | some name => some s!"declaration name `{name}` is repeated"
            | none => none
  | .definitionDecl definition =>
      match typeParameterError definition.name definition.typeParameters with
      | some error => some error
      | none => match duplicateName (definition.parameters.map (·.1)) with
          | some name => some s!"definition parameter `{name}` is repeated"
          | none => none
  | .ruleDecl rule =>
      let shape := match rule.kind, rule.lhs, rule.rhs, rule.conclusion with
        | .rewrite, some _, some _, _ => none
        | .rewrite, _, _, _ => some "rewrite rules need both a left and right side"
        | .inference, _, _, some _ => none
        | .theorem, _, _, some _ => none
        | .inference, _, _, _ => some "inference rules need a conclusion"
        | .theorem, _, _, _ => some "theorems need a conclusion"
        | _, _, _, _ => some "this declaration kind is not a rule"
      shape.orElse fun () =>
        (typeParameterError rule.name rule.typeParameters).orElse fun () =>
          match duplicateName (rule.parameters.map (·.1)) with
          | some name => some s!"rule parameter `{name}` is repeated"
          | none => none

private def validate (env : Env) (theory : Spec) : List String :=
  let names := theory.symbols.map (·.name)
  let declarationNames := declarationNamesAll theory.declarations
  let duplicate := firstDuplicate [] names
  let duplicateDeclaration := duplicateName declarationNames
  let symbolDeclarationConflict := theory.symbols.find? fun symbol =>
    declarationNames.contains symbol.name &&
      !(symbol.kind == .expression && isDefinitionName theory.declarations symbol.name)
  let reserved := theory.symbols.find? (fun symbol =>
    (coreSymbols.find? (·.name == symbol.name)).isSome)
  let reservedDeclaration := theory.declarations.find? (fun declaration =>
    (coreSymbols.find? (·.name == declaration.name)).isSome)
  let imported := theory.imports.find? (fun name =>
    name != core.name && (lookupTheory? env name).isNone)
  let importedSymbols := symbolsIn env theory.imports
  let importedDuplicate := firstDuplicate [] (importedSymbols.map (·.2.name))
  let shadowed := theory.symbols.find? (fun symbol =>
    importedSymbols.any (fun (_, imported) => imported.name == symbol.name))
  let importedDeclarations := declarationsIn env theory.imports
  let importedDeclarationNames := importedDeclarations.map (·.2.name)
  let symbolShadowedDeclaration := theory.symbols.find?
    (fun symbol => importedDeclarationNames.contains symbol.name)
  let declarationShadowedSymbol := theory.declarations.find?
    (fun declaration => importedSymbols.any (fun (_, symbol) => symbol.name == declaration.name))
  let shadowedDeclaration := theory.declarations.find? (fun declaration =>
    importedDeclarationNames.contains declaration.name)
  let declarationProblem := theory.declarations.findSome? declarationError
  let duplicateTheory := (lookupTheory? env theory.name).isSome
  let errors := []
  let errors := if theory.name == core.name then
    errors ++ [s!"theory `{theory.name}` is reserved"] else errors
  let errors := if duplicateTheory then
    errors ++ [s!"theory `{theory.name}` is already registered"] else errors
  let errors := match duplicate with
    | some name => errors ++ [s!"symbol `{name}` is declared more than once"]
    | none => errors
  let errors := match duplicateDeclaration with
    | some name => errors ++ [s!"declaration `{name}` is declared more than once"]
    | none => errors
  let errors := match symbolDeclarationConflict with
    | some symbol => errors ++ [s!"symbol and declaration `{symbol.name}` share a name"]
    | none => errors
  let errors := match reserved with
    | some symbol => errors ++ [s!"symbol `{symbol.name}` is reserved by the core prelude"]
    | none => errors
  let errors := match reservedDeclaration with
    | some declaration =>
        errors ++ [s!"declaration `{declaration.name}` is reserved by the core prelude"]
    | none => errors
  let errors := match importedDuplicate with
    | some name => errors ++ [s!"imported symbol `{name}` is ambiguous"]
    | none => errors
  let errors := match shadowed with
    | some symbol => errors ++ [s!"symbol `{symbol.name}` shadows an imported symbol"]
    | none => errors
  let errors := match symbolShadowedDeclaration with
    | some symbol =>
        errors ++ [s!"symbol `{symbol.name}` shadows an imported declaration"]
    | none => errors
  let errors := match declarationShadowedSymbol with
    | some declaration =>
        errors ++ [s!"declaration `{declaration.name}` shadows an imported symbol"]
    | none => errors
  let errors := match shadowedDeclaration with
    | some declaration =>
        errors ++ [s!"declaration `{declaration.name}` shadows an imported declaration"]
    | none => errors
  let errors := match declarationProblem with
    | some error => errors ++ [error]
    | none => errors
  match imported with
  | some name => errors ++ [s!"theory `{name}` is not registered"]
  | none => errors

def add (env : Env) (theory : Spec) : Except String Env :=
  let theory := canonicalize theory
  match validate env theory with
  | error :: _ => .error error
  | [] => .ok { env with theories := theory :: env.theories }

def register (specs : List Spec) : Except String Env :=
  specs.foldlM add empty

/-- Compatibility lookup for callers that have no component-specific scope yet. -/
def lookup? (env : Env) (name : String) : Option (String × Symbol) :=
  lookupIn? env (env.theories.map (·.name)) name

def isIdentifierIn (env : Env) (roots : List String) (name : String) : Bool :=
  (lookupIn? env roots name).isSome || isDeclarationIn env roots name

def isIdentifier (env : Env) (name : String) : Bool :=
  isIdentifierIn env (env.theories.map (·.name)) name

def typeIn? (env : Env) (roots : List String) (name : String) : Option Typing.Ty :=
  match (lookupIn? env roots name).bind (·.2.type) with
  | some type => some type
  | none =>
      match constructor? env roots name with
      | some (_, datatype, constructor) => some (constructor.type datatype)
      | none => (declaration? env roots name).bind (·.2.expressionType?)

def type? (env : Env) (name : String) : Option Typing.Ty :=
  typeIn? env (env.theories.map (·.name)) name

#guard (lookup? empty "BOOL").isSome
#guard type? empty "TRUE" == some .bool
#guard (lookupIn? empty [] "TRUE").isSome
#guard (lookupIn? empty [] "notVisible").isNone
#guard namesWithApplication empty [] .total |>.contains "bool"

private def imported : Env :=
  match add empty
      { name := "Base", symbols :=
        [{ name := "LIMIT", kind := .constant, type := some .int
           description := "An imported constant." }] } with
  | .error _ => empty
  | .ok env =>
    match add env { name := "Derived", imports := ["Base"] } with
    | .ok env => env
    | .error _ => empty

#guard typeIn? imported ["Derived"] "LIMIT" == some .int
#guard typeIn? imported [] "LIMIT" == none
#guard match add empty { name := "Bad", symbols := coreSymbols } with
  | .error _ => true
  | .ok _ => false
#guard match add imported
    ({ name := "Conflict", imports := ["Derived"]
       symbols :=
         [Symbol.mk "LIMIT" .constant (some .int) "A conflicting constant." none []
            (SymbolId.unqualified "LIMIT") SourceRange.synthetic] } : Spec) with
  | .error _ => true
  | .ok _ => false
#guard match add empty
    ({ name := "LocalConflict", symbols :=
        [Symbol.mk "Thing" .constant (some .int) "A symbol." none []
          (SymbolId.unqualified "Thing") SourceRange.synthetic]
       declarations := [.dataType { name := "Thing", constructors :=
         [{ name := "ctor" }] }] } : Spec) with
  | .error _ => true
  | .ok _ => false

private def declarationEnv : Env :=
  match add empty
      { name := "Data", declarations :=
        [.dataType (Datatype.mk "Colour" []
          [Constructor.mk "red" [], Constructor.mk "blue" []]),
         .definitionDecl { name := "zero", result := .int, body := .num 0 }] } with
  | .ok env => env
  | .error _ => empty

#guard isDeclarationIn declarationEnv ["Data"] "Colour"
#guard (declaration? declarationEnv ["Data"] "Colour").isSome
#guard typeIn? declarationEnv ["Data"] "red" == some (.given "Colour")
#guard typeIn? declarationEnv ["Data"] "Colour" == none
#guard typeIn? declarationEnv ["Data"] "zero" == some .int
#guard namesWithApplication declarationEnv ["Data"] .total |>.contains "zero"

private def rewriteEnv : Env :=
  match add empty
      { name := "Rewrite", declarations := [.ruleDecl
          { name := "add_zero", kind := .rewrite, parameters := [("x", .int)]
            lhs := some (.bin "+" (.id "x") (.num 0)), rhs := some (.id "x") }] } with
  | .ok env => env
  | .error _ => empty

private def binderRewriteEnv : Env :=
  match add empty
      { name := "BinderRewrite", declarations :=
        [.ruleDecl
          { name := "singleton_union_empty", kind := .rewrite,
            parameters := [("x", .int)]
            lhs := some (.bin "∪" (.set [.id "x"]) (.set []))
            rhs := some (.set [.id "x"]) },
         .ruleDecl
          { name := "forall_add_zero", kind := .rewrite,
            parameters := [("x", .int)]
            lhs := some (.bind "∀" (.id "y")
              (.bin "=" (.bin "+" (.id "x") (.num 0)) (.id "y")))
            rhs := some (.bind "∀" (.id "y") (.bin "=" (.id "x") (.id "y"))) },
         .ruleDecl
          { name := "comprehension_add_zero", kind := .rewrite,
            parameters := [("x", .int)]
            lhs := some (.bind "{" (.id "y")
              (.bin "∣" (.bin "=" (.id "x") (.id "y"))
                (.bin "+" (.id "x") (.num 0))))
            rhs := some (.bind "{" (.id "y")
              (.bin "∣" (.bin "=" (.id "x") (.id "y")) (.id "x"))) }] } with
  | .ok env => env
  | .error _ => empty

private def parseFormula! (source : String) : Formula.Term :=
  (Formula.parse source).toOption.getD (.id "?")

#guard Definition.type
    { name := "increment", parameters := [("x", .int)], result := .int, body := .num 0 }
    == .pow (.prod .int .int)
#guard match Formula.parse "1 + 0" with
  | .ok term => Formula.alphaEq (normalize rewriteEnv ["Rewrite"] term) (.num 1)
  | .error _ => false
#guard Formula.alphaEq
  (normalize binderRewriteEnv ["BinderRewrite"] (parseFormula! "{1} ∪ {}"))
  (parseFormula! "{1}")
#guard Formula.alphaEq
  (normalize binderRewriteEnv ["BinderRewrite"] (parseFormula! "∀z · (1 + 0) = z"))
  (parseFormula! "∀z · 1 = z")
#guard Formula.alphaEq
  (normalize binderRewriteEnv ["BinderRewrite"]
    (parseFormula! "{z · 1 = z ∣ 1 + 0}"))
  (parseFormula! "{z · 1 = z ∣ 1}")
#guard Formula.alphaEq
  (normalize binderRewriteEnv ["BinderRewrite"] (parseFormula! "∀z · z + 0 = z"))
  (parseFormula! "∀z · z + 0 = z")

#guard match add empty
    { name := "EmptyData", declarations := [.dataType (Datatype.mk "EmptyData" [] [])] } with
  | .error _ => true
  | .ok _ => false

end EventB.Theory
