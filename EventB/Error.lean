/-
Structured errors shared by Event-B's public reader, checker, and trust boundaries.

Private implementation details may still use strings. Public APIs return this type so callers
can preserve the error domain and source path until the presentation layer renders it.
-/

namespace EventB

inductive ErrorKind where
  | formula
  | model
  | rossi
  | theory
  | typing
  | trust
  | prover
  | io
  | cli
  deriving BEq, DecidableEq, Repr, Inhabited

structure Error where
  kind : ErrorKind
  message : String
  path : Option String := none
  context : List String := []
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Error

def formula (message : String) : Error := { kind := .formula, message }

def model (message : String) : Error := { kind := .model, message }

def rossi (message : String) : Error := { kind := .rossi, message }

def theory (message : String) : Error := { kind := .theory, message }

def typing (message : String) : Error := { kind := .typing, message }

def trust (message : String) : Error := { kind := .trust, message }

def prover (message : String) : Error := { kind := .prover, message }

def io (message : String) : Error := { kind := .io, message }

def cli (message : String) : Error := { kind := .cli, message }

def withPath (error : Error) (path : String) : Error :=
  { error with path := some path }

def withContext (error : Error) (context : String) : Error :=
  { error with context := context :: error.context }

def render (error : Error) : String :=
  String.intercalate ": " (error.path.toList ++ error.context.reverse ++ [error.message])

instance : ToString Error where
  toString := render

end Error

end EventB
