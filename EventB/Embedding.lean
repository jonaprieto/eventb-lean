/-
Kernel-native interpretation of resolved Event-B types.

The formula AST and theory environment remain syntax-level data. This module gives the
translation layer a typed target for resolved types without inventing values for unresolved
metavariables or untyped theory declarations.
-/

import EventB.Theory

namespace EventB.Embedding

abbrev EventSet (α : Type) := α → Prop

structure Signature where
  carrier : String → Type

private def typeOf? (signature : Signature) : Typing.Ty → Option Type
  | .given name => some (signature.carrier name)
  | .int => some Int
  | .bool => some Bool
  | .pow type => (typeOf? signature type).map EventSet
  | .prod left right => do
      let left ← typeOf? signature left
      let right ← typeOf? signature right
      return left × right
  | .mvar _ => none

def type? (signature : Signature) (type : Typing.Ty) : Option Type :=
  typeOf? signature type

def symbolType? (signature : Signature) (symbol : Prelude.Symbol) : Option Type :=
  symbol.type.bind (type? signature)

def embeddable (signature : Signature) (env : Theory.Env) : List String :=
  env.theories.flatMap fun theory =>
    theory.symbols.filterMap fun symbol =>
      if symbol.type.isSome && (symbolType? signature symbol).isNone then
        some s!"{theory.name}.{symbol.name}"
      else none

#guard (type? { carrier := fun _ => Nat } .int).isSome
#guard (type? { carrier := fun _ => Nat } (.pow .bool)).isSome
#guard (type? { carrier := fun _ => Nat } (.mvar 0)).isNone
#guard (embeddable { carrier := fun _ => Nat } Theory.empty).isEmpty

end EventB.Embedding
