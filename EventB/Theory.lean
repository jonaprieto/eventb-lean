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
  deriving BEq, Repr, Inhabited

structure Rule where
  name : String
  kind : DeclarationKind
  parameters : List (String × Typing.Ty) := []
  premises : List Formula.Term := []
  lhs : Option Formula.Term := none
  rhs : Option Formula.Term := none
  conclusion : Option Formula.Term := none
  deriving BEq, Repr, Inhabited

inductive Declaration where
  | datatype (value : Datatype)
  | definition (value : Definition)
  | rule (value : Rule)
  deriving BEq, Repr, Inhabited

def Declaration.name : Declaration → String
  | .datatype value => value.name
  | .definition value => value.name
  | .rule value => value.name

def Declaration.kind : Declaration → DeclarationKind
  | .datatype _ => .datatype
  | .definition value => match value.kind with
    | .definitional => .definition
    | .axiomatic => .axiom
  | .rule value => value.kind

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
  (symbolsIn env roots).filterMap fun (_, symbol) =>
    if symbol.application == some application then some symbol.name else none

def definedness? (env : Env) (roots : List String) (name : String) : List Definedness :=
  (lookupIn? env roots name).map (·.2.definedness) |>.getD []

def declaration? (env : Env) (roots : List String) (name : String) :
    Option (String × Declaration) :=
  declarationsIn env roots |>.find? (·.2.name == name)

def isDeclarationIn (env : Env) (roots : List String) (name : String) : Bool :=
  (declaration? env roots name).isSome

private def declarationNames (declarations : List Declaration) : List String :=
  declarations.map Declaration.name

private def constructorNames (datatype : Datatype) : List String :=
  datatype.constructors.map (·.name)

private def declarationParts (declaration : Declaration) : List String :=
  match declaration with
  | .datatype datatype => datatype.name :: constructorNames datatype
  | .definition definition => [definition.name]
  | .rule rule => [rule.name]

private def declarationNamesAll (declarations : List Declaration) : List String :=
  declarations.flatMap declarationParts

private def duplicateName (names : List String) : Option String := firstDuplicate [] names

private def declarationError (declaration : Declaration) : Option String :=
  match declaration with
  | .datatype datatype =>
      if datatype.constructors.isEmpty then
        some s!"datatype `{datatype.name}` needs a constructor"
      else match duplicateName (datatype.parameters ++ constructorNames datatype) with
        | some name => some s!"declaration name `{name}` is repeated"
        | none => none
  | .definition definition =>
      match duplicateName (definition.parameters.map (·.1)) with
      | some name => some s!"definition parameter `{name}` is repeated"
      | none => none
  | .rule rule =>
      let shape := match rule.kind, rule.lhs, rule.rhs, rule.conclusion with
        | .rewrite, some _, some _, _ => none
        | .rewrite, _, _, _ => some "rewrite rules need both a left and right side"
        | .inference, _, _, some _ => none
        | .theorem, _, _, some _ => none
        | .inference, _, _, _ => some "inference rules need a conclusion"
        | .theorem, _, _, _ => some "theorems need a conclusion"
        | _, _, _, _ => some "this declaration kind is not a rule"
      shape.orElse fun () => match duplicateName (rule.parameters.map (·.1)) with
        | some name => some s!"rule parameter `{name}` is repeated"
        | none => none

private def validate (env : Env) (theory : Spec) : List String :=
  let names := theory.symbols.map (·.name)
  let declarationNames := declarationNamesAll theory.declarations
  let duplicate := firstDuplicate [] names
  let duplicateDeclaration := duplicateName declarationNames
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
  (lookup? env name).isSome

def typeIn? (env : Env) (roots : List String) (name : String) : Option Typing.Ty :=
  (lookupIn? env roots name).bind (·.2.type)

def type? (env : Env) (name : String) : Option Typing.Ty :=
  (lookup? env name).bind (·.2.type)

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
         [Symbol.mk "LIMIT" .constant (some .int) "A conflicting constant." none []] } : Spec) with
  | .error _ => true
  | .ok _ => false

private def declarationEnv : Env :=
  match add empty
      { name := "Data", declarations :=
        [.datatype (Datatype.mk "Colour" []
          [Constructor.mk "red" [], Constructor.mk "blue" []])] } with
  | .ok env => env
  | .error _ => empty

#guard isDeclarationIn declarationEnv ["Data"] "Colour"
#guard (declaration? declarationEnv ["Data"] "Colour").isSome
#guard match add empty
    { name := "EmptyData", declarations := [.datatype (Datatype.mk "EmptyData" [] [])] } with
  | .error _ => true
  | .ok _ => false

end EventB.Theory
