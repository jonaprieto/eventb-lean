/-
The built-in Event-B mathematical prelude.

This is implicit in every Event-B project. User theories are layered on top of it
rather than adding more special cases to the parser, checker, or POG.
-/

import EventB.Source
import EventB.Typing.Type

namespace EventB.Prelude

open EventB.Typing

inductive SymbolKind where
  | carrierSet
  | constant
  | predicate
  | expression
  deriving BEq, Repr, Inhabited

inductive ApplicationKind where
  | total
  | wellDefined
  deriving BEq, Repr, Inhabited

inductive Definedness where
  | finite
  | nonempty
  | lowerBound
  | upperBound
  deriving BEq, Repr, Inhabited

structure SymbolId where
  owner : String
  name : String
  deriving BEq, Repr, Inhabited

namespace SymbolId

def unqualified (name : String) : SymbolId :=
  { owner := "", name }

def qualified (owner name : String) : SymbolId :=
  { owner, name }

def display (id : SymbolId) : String :=
  if id.owner.isEmpty then id.name else id.owner ++ "::" ++ id.name

end SymbolId

structure Symbol where
  name : String
  kind : SymbolKind
  type : Option Ty
  description : String
  application : Option ApplicationKind := none
  definedness : List Definedness := []
  id : SymbolId := SymbolId.unqualified name
  source : SourceRange := SourceRange.synthetic
  deriving Repr, Inhabited

private def carrier (name description : String) : Symbol :=
  { name, kind := .carrierSet, type := some (.pow .int), description,
    id := SymbolId.unqualified name, source := SourceRange.synthetic }

private def constant (name description : String) (type : Ty) : Symbol :=
  { name, kind := .constant, type := some type, description,
    id := SymbolId.unqualified name, source := SourceRange.synthetic }

private def predicate (name description : String) (application : ApplicationKind) : Symbol :=
  { name, kind := .predicate, type := none, description, application := some application,
    id := SymbolId.unqualified name, source := SourceRange.synthetic }

private def expression (name description : String) (application : ApplicationKind)
    (definedness : List Definedness := []) : Symbol :=
  { name, kind := .expression, type := none, description, application := some application,
    definedness, id := SymbolId.unqualified name, source := SourceRange.synthetic }

private def coreSource : SourceRange := SourceRange.synthetic "EventB.Prelude"

private def coreSymbol (symbol : Symbol) : Symbol :=
  { symbol with id := SymbolId.qualified "EventB.Core" symbol.name, source := coreSource }

def coreSymbols : List Symbol :=
  [ carrier "ℤ" "The set of all integers."
  , carrier "ℕ" "The set of natural numbers."
  , carrier "ℕ1" "The set of positive natural numbers."
  , { name := "BOOL", kind := .carrierSet, type := some (.pow .bool)
      description := "The predefined Boolean carrier set.",
      id := SymbolId.unqualified "BOOL", source := SourceRange.synthetic }
  , constant "TRUE" "The Boolean true value." .bool
  , constant "FALSE" "The Boolean false value." .bool
  , { name := "⊤", kind := .predicate, type := none
      description := "The always-true predicate.",
      id := SymbolId.unqualified "⊤", source := SourceRange.synthetic }
  , { name := "⊥", kind := .predicate, type := none
      description := "The always-false predicate.",
      id := SymbolId.unqualified "⊥", source := SourceRange.synthetic }
  , predicate "finite" "The predicate that an expression denotes a finite set." .total
  , predicate "partition" "The predicate that sets form a partition." .total
  , expression "card" "The cardinality of a finite set." .wellDefined [.finite]
  , expression "min" "The minimum of a non-empty bounded integer set." .wellDefined
      [.nonempty, .lowerBound]
  , expression "max" "The maximum of a non-empty bounded integer set." .wellDefined
      [.nonempty, .upperBound]
  , expression "dom" "The domain of a relation." .total
  , expression "ran" "The range of a relation." .total
  , expression "bool" "The Boolean value of a predicate." .total
  , expression "union" "The union of a set of sets." .total
  , expression "inter" "The intersection of a non-empty set of sets." .wellDefined
      [.nonempty]
  , expression "succ" "The successor of an integer." .total
  , expression "pred" "The predecessor of an integer." .total
  , expression "prj1" "The first projection of a relation." .total
  , expression "prj2" "The second projection of a relation." .total
  , expression "id" "The identity relation on a set." .total
  ] |>.map coreSymbol

def lookup? (name : String) : Option Symbol :=
  coreSymbols.find? (·.name == name)

def isIdentifier (name : String) : Bool :=
  (lookup? name).isSome

def type? (name : String) : Option Ty :=
  (lookup? name).bind (·.type)

def application? (name : String) : Option ApplicationKind :=
  (lookup? name).bind (·.application)

#guard (lookup? "BOOL").isSome
#guard type? "TRUE" == some .bool
#guard application? "card" == some .wellDefined
#guard (lookup? "TRUE").map (·.id) == some (SymbolId.qualified "EventB.Core" "TRUE")

end EventB.Prelude
