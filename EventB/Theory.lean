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

def add (env : Env) (theory : Spec) : Env :=
  { env with theories := theory :: env.theories }

def lookupTheory? (env : Env) (name : String) : Option Spec :=
  env.theories.find? (·.name == name)

def lookup? (env : Env) (name : String) : Option (String × Symbol) :=
  env.theories.findSome? fun theory =>
    theory.symbols.find? (fun symbol => symbol.name == name) |>.map (theory.name, ·)

def isIdentifier (env : Env) (name : String) : Bool :=
  (lookup? env name).isSome

def type? (env : Env) (name : String) : Option Typing.Ty :=
  (lookup? env name).bind (·.2.type)

#guard (lookup? empty "BOOL").isSome
#guard type? empty "TRUE" == some .bool

end EventB.Theory
