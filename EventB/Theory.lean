/-
The native Event-B theory environment.

The core prelude is always present. User theories will add symbols and imports here;
model components remain a separate layer in the environment.
-/

import EventB.Prelude

namespace EventB.Theory

open EventB.Prelude

structure Spec where
  name : String
  imports : List String := []
  symbols : List Symbol := []
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

private def validate (env : Env) (theory : Spec) : List String :=
  let names := theory.symbols.map (·.name)
  let duplicate := firstDuplicate [] names
  let reserved := theory.symbols.find? (fun symbol =>
    (coreSymbols.find? (·.name == symbol.name)).isSome)
  let imported := theory.imports.find? (fun name =>
    name != core.name && (lookupTheory? env name).isNone)
  let duplicateTheory := (lookupTheory? env theory.name).isSome
  let errors := []
  let errors := if theory.name == core.name then
    errors ++ [s!"theory `{theory.name}` is reserved"] else errors
  let errors := if duplicateTheory then
    errors ++ [s!"theory `{theory.name}` is already registered"] else errors
  let errors := match duplicate with
    | some name => errors ++ [s!"symbol `{name}` is declared more than once"]
    | none => errors
  let errors := match reserved with
    | some symbol => errors ++ [s!"symbol `{symbol.name}` is reserved by the core prelude"]
    | none => errors
  match imported with
  | some name => errors ++ [s!"theory `{name}` is not registered"]
  | none => errors

def add (env : Env) (theory : Spec) : Except String Env :=
  match validate env theory with
  | error :: _ => .error error
  | [] => .ok { env with theories := theory :: env.theories }

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

def namesWithApplication (env : Env) (roots : List String) (application : ApplicationKind) :
    List String :=
  (symbolsIn env roots).filterMap fun (_, symbol) =>
    if symbol.application == some application then some symbol.name else none

def definedness? (env : Env) (roots : List String) (name : String) : List Definedness :=
  (lookupIn? env roots name).map (·.2.definedness) |>.getD []

/-- Compatibility lookup for callers that have no component-specific scope yet. -/
def lookup? (env : Env) (name : String) : Option (String × Symbol) :=
  lookupIn? env (env.theories.map (·.name)) name

def isIdentifierIn (env : Env) (roots : List String) (name : String) : Bool :=
  (lookupIn? env roots name).isSome

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

end EventB.Theory
