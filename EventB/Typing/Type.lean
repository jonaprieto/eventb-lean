/-
Event-B types. The whole language is given sets, `ℤ`, `BOOL`, powerset and product:
27 distinct types cover the entire vendored corpus.

`print` has to match Rodin byte for byte, because the `.bpo` type strings are the P2
gate. That pins two conventions: `×` is left-associative and printed without brackets
when it nests to the left (`ℙ(ℤ×ℤ×ℤ)`), and brackets appear only when a product nests to
the right.
-/

namespace EventB.Typing

inductive Ty where
  /-- A carrier set, from `org.eventb.core.carrierSet`, or a given set of the project. -/
  | given : String → Ty
  | int  : Ty
  | bool : Ty
  | pow  : Ty → Ty
  | prod : Ty → Ty → Ty
  /-- Unification variable, resolved through the substitution in `Infer`. -/
  | mvar : Nat → Ty
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Node count, used to bound the substitution traversals in `Infer`. -/
def Ty.size : Ty → Nat
  | .given _ | .int | .bool | .mvar _ => 1
  | .pow t => t.size + 1
  | .prod a b => a.size + b.size + 1

def Ty.print : Ty → String
  | .given s => s
  | .int => "ℤ"
  | .bool => "BOOL"
  | .pow t => "ℙ(" ++ t.print ++ ")"
  | .prod a b =>
      -- Left-nesting is implicit, right-nesting needs brackets, matching Rodin.
      let right := match b with
        | .prod _ _ => "(" ++ b.print ++ ")"
        | _ => b.print
      a.print ++ "×" ++ right
  | .mvar n => s!"?{n}"

mutual

/-- Same shape as the formula lexer: every branch consumes at least one character, but
that fact lives inside `takeWhile` and the literal patterns rather than in a type, so
`fuel` states it. Seeded at the input length, it cannot run out on a terminating scan. -/
private def parseGo : Nat → List Char → Option (Ty × List Char)
  | 0, _ => none
  | fuel + 1, cs => do
    let (lhs, rest) ← parseAtom fuel cs
    parseProducts fuel lhs rest

private def parseProducts : Nat → Ty → List Char → Option (Ty × List Char)
  | 0, lhs, cs => some (lhs, cs)
  | fuel + 1, lhs, cs =>
    match cs with
    | '×' :: rest => do
        let (rhs, rest) ← parseAtom fuel rest
        parseProducts fuel (.prod lhs rhs) rest
    | _ => some (lhs, cs)

private def parseAtom : Nat → List Char → Option (Ty × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match cs with
    | 'ℙ' :: '(' :: rest => do
        let (inner, rest) ← parseGo fuel rest
        match rest with
        | ')' :: rest => some (.pow inner, rest)
        | _ => none
    | '(' :: rest => do
        let (inner, rest) ← parseGo fuel rest
        match rest with
        | ')' :: rest => some (inner, rest)
        | _ => none
    | 'ℤ' :: rest => some (.int, rest)
    | cs =>
        let name := cs.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'')
        if name.isEmpty then none
        else
          let s := String.ofList name
          some (if s == "BOOL" then .bool else .given s, cs.drop name.length)

end

def Ty.parse (s : String) : Option Ty :=
  let cs := s.toList
  parseGo (cs.length + 1) cs |>.bind fun (t, rest) => if rest.isEmpty then some t else none

end EventB.Typing
