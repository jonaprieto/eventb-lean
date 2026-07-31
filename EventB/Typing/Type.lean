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
  deriving BEq, Repr, Inhabited

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

/-- Rodin's spelling, parsed back so the gate can compare trees rather than strings and
report a mismatch instead of a diff of two lines of Unicode. -/
partial def Ty.parse (s : String) : Option Ty :=
  go s.toList |>.bind fun (t, rest) => if rest.isEmpty then some t else none
where
  go (cs : List Char) : Option (Ty × List Char) := do
    let (lhs, rest) ← atom cs
    products lhs rest
  products (lhs : Ty) (cs : List Char) : Option (Ty × List Char) :=
    match cs with
    | '×' :: rest => do
        let (rhs, rest) ← atom rest
        products (.prod lhs rhs) rest
    | _ => some (lhs, cs)
  atom (cs : List Char) : Option (Ty × List Char) :=
    match cs with
    | 'ℙ' :: '(' :: rest => do
        let (inner, rest) ← go rest
        match rest with
        | ')' :: rest => some (.pow inner, rest)
        | _ => none
    | '(' :: rest => do
        let (inner, rest) ← go rest
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

end EventB.Typing
