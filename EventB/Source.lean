/-
Stable source metadata shared by native theories and model diagnostics.

Lines are one-based and columns are zero-based, matching Lean's source positions and
the line numbering used by the Rossi reader.
-/

namespace EventB

structure Position where
  line : Nat
  column : Nat
  deriving BEq, Repr, Inhabited

structure SourceRange where
  file : String
  beginPos : Position
  finishPos : Position
  deriving BEq, Repr, Inhabited

namespace SourceRange

def synthetic (file : String := "<generated>") : SourceRange :=
  { file, beginPos := { line := 1, column := 0 }, finishPos := { line := 1, column := 0 } }

def display (range : SourceRange) : String :=
  s!"{range.file}:{range.beginPos.line}:{range.beginPos.column + 1}-" ++
    s!"{range.finishPos.line}:{range.finishPos.column + 1}"

end SourceRange

end EventB
