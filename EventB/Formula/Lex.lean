/-
Tokens for Event-B formulas.

Rodin stores formulas already normalised to Unicode, so the corpus never exercises the
ASCII spellings. They are in the table anyway: CamilleX accepts both (see
`docs/XMachine.xtext`), and a lexer that only knows `∈` would reject hand-written source
the moment anyone types `:`. Longest match is what makes the two live together, since
`<<:` must not be read as `<` then `<:`.
-/

namespace EventB.Formula

inductive Tok where
  | id  : String → Tok
  | num : Nat → Tok
  /-- Canonical Unicode spelling, so the parser never sees an alias. -/
  | op  : String → Tok
  deriving BEq, Repr, Inhabited

def Tok.render : Tok → String
  | .id s  => s
  | .num n => toString n
  | .op s  => s

/-- Alias to canonical spelling. Longest match wins, so order here does not matter, but
every canonical operator must also map to itself. -/
def operators : List (String × String) :=
  -- Predicate calculus.
  [("⇔", "⇔"), ("<=>", "⇔"), ("⇒", "⇒"), ("=>", "⇒"),
   ("∧", "∧"), ("&", "∧"), ("∨", "∨"), ("or", "∨"), ("¬", "¬"), ("not", "¬"),
   ("⊤", "⊤"), ("true", "⊤"), ("⊥", "⊥"), ("false", "⊥"),
   ("∀", "∀"), ("!", "∀"), ("∃", "∃"), ("#", "∃"),
   -- Relational predicates.
   ("=", "="), ("≠", "≠"), ("/=", "≠"), ("≤", "≤"), ("=<", "≤"), ("<", "<"),
   ("≥", "≥"), (">=", "≥"), (">", ">"),
   ("∈", "∈"), (":", "∈"), ("∉", "∉"), ("/:", "∉"),
   ("⊂", "⊂"), ("<<:", "⊂"), ("⊄", "⊄"), ("/<<:", "⊄"),
   ("⊆", "⊆"), ("<:", "⊆"), ("⊈", "⊈"), ("/<:", "⊈"),
   -- Relation and function arrows.
   ("↔", "↔"), ("<->", "↔"), ("⇸", "⇸"), ("+->", "⇸"), ("→", "→"), ("-->", "→"),
   -- Rodin spells the three surjective-relation arrows and the override operator with
   -- private-use codepoints, which have no standard Unicode equivalent.
   ("", ""), ("<<->", ""), ("", ""), ("<->>", ""),
   ("", ""), ("<<->>", ""),
   ("⤔", "⤔"), (">+>", "⤔"), ("↣", "↣"), (">->", "↣"),
   ("⤀", "⤀"), ("+>>", "⤀"), ("↠", "↠"), ("->>", "↠"), ("⤖", "⤖"), (">->>", "⤖"),
   -- Sets, relations, functions.
   ("∅", "∅"), ("∩", "∩"), ("/\\", "∩"), ("∪", "∪"), ("\\/", "∪"), ("∖", "∖"),
   ("×", "×"), ("**", "×"), ("↦", "↦"), ("|->", "↦"), (",,", "↦"),
   ("", ""), ("<+", ""), ("∘", "∘"), ("circ", "∘"), (";", ";"),
   ("⊗", "⊗"), ("><", "⊗"), ("∥", "∥"), ("||", "∥"), ("∼", "∼"), ("~", "∼"),
   ("◁", "◁"), ("<|", "◁"), ("⩤", "⩤"), ("<<|", "⩤"),
   ("▷", "▷"), ("|>", "▷"), ("⩥", "⩥"), ("|>>", "⩥"),
   ("λ", "λ"), ("%", "λ"), ("⋂", "⋂"), ("INTER", "⋂"), ("⋃", "⋃"), ("UNION", "⋃"),
   -- Arithmetic.
   ("‥", "‥"), ("..", "‥"), ("+", "+"), ("−", "−"), ("-", "−"),
   ("∗", "∗"), ("*", "∗"), ("÷", "÷"), ("/", "÷"), ("^", "^"), ("mod", "mod"),
   -- Assignment, in actions rather than predicates.
   ("≔", "≔"), (":=", "≔"), (":∈", ":∈"), (":|", ":∣"), (":∣", ":∣"),
   -- Type constructors written as operators.
   ("ℙ1", "ℙ1"), ("POW1", "ℙ1"), ("ℙ", "ℙ"), ("POW", "ℙ"),
   ("ℕ1", "ℕ1"), ("NAT1", "ℕ1"), ("ℕ", "ℕ"), ("NAT", "ℕ"), ("ℤ", "ℤ"), ("INT", "ℤ"),
   -- Structure.
   ("(", "("), (")", ")"), ("{", "{"), ("}", "}"), ("[", "["), ("]", "]"),
   (",", ","), ("·", "·"), (".", "·"), ("∣", "∣"), ("|", "∣")]

/-- Longest first, so `<<:` is never read as `<` followed by `<:`. Held as a `Char`
list per alias because the scanner works on `List Char`, and sorted once: re-sorting a
130-entry table on every token turned the corpus scan into minutes. -/
def operatorTable : Array (List Char × String) :=
  (operators.mergeSort (fun a b => b.1.length < a.1.length)).map
    (fun (alias, canon) => (alias.toList, canon)) |>.toArray

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Operator aliases spelled with letters (`or`, `mod`, `NAT`) must not swallow the head
of an identifier: `order` is one name, not `or` followed by `der`. -/
private def aliasFits (alias rest : List Char) : Bool :=
  if alias.all isIdentRest then
    match rest.drop alias.length with
    | c :: _ => !isIdentRest c
    | [] => true
  else
    true

private def matchOperator (table : Array (List Char × String)) (cs : List Char) :
    Option (String × List Char) :=
  table.findSome? fun (a, canon) =>
    -- `!a.isEmpty` is load-bearing: an empty alias matches everywhere and consumes
    -- nothing, so the scanner would spin forever on the first character.
    if !a.isEmpty && a.isPrefixOf cs && aliasFits a cs then some (canon, cs.drop a.length)
    else none

-- The table is threaded rather than referenced globally: Lean recomputes a nullary
-- `def` at each use site, and re-sorting 130 aliases per token made the corpus scan
-- take minutes instead of milliseconds.
private partial def go (table : Array (List Char × String)) (acc : List Tok) :
    List Char → Except String (List Tok)
  | [] => .ok acc.reverse
  | c :: cs =>
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      go table acc cs
    else if isIdentStart c then
      -- Keyword-shaped operators (`mod`, `NAT`, `UNION`) are checked first, so the ident
      -- branch only sees names.
      match matchOperator table (c :: cs) with
      | some (canon, rest) => go table (.op canon :: acc) rest
      | none =>
        let name := (c :: cs).takeWhile isIdentRest
        go table (.id (String.ofList name) :: acc) ((c :: cs).drop name.length)
    else if c.isDigit then
      let ds := (c :: cs).takeWhile Char.isDigit
      let n := ds.foldl (fun n d => n * 10 + (d.toNat - 48)) 0
      go table (.num n :: acc) ((c :: cs).drop ds.length)
    else
      match matchOperator table (c :: cs) with
      | some (canon, rest) => go table (.op canon :: acc) rest
      | none => .error s!"unexpected character {c}"

/-- `mod` is the only word-shaped operator Rodin treats as infix; the rest of the word
operators (`card`, `dom`, `bool`, ...) are ordinary identifiers applied to an argument,
so the lexer leaves them alone. -/
def lex (s : String) : Except String (List Tok) :=
  go operatorTable [] s.toList

end EventB.Formula
