/-
Event-B formulas: AST, precedence-climbing parser, printer.

Predicates and expressions share one `Term`. Rodin separates them, but the separation is
a typing question and belongs to P2; keeping one syntax tree means the parser never has
to guess which side of the grammar it is on before it has seen the operator.

Where Rodin uses a pairwise operator compatibility table, this uses precedence levels
plus an associativity flag. The difference shows up only on expressions Rodin rejects
outright, such as `a ∈ b ∈ c` (non-associative here too, so it is rejected) or
`a ∪ b ∩ c` (Rodin demands parentheses; this parser reads it left to right). Tightening
that to the real table is P2 work, once types can tell the cases apart.
-/

import EventB.Formula.Lex

namespace EventB.Formula

inductive Term where
  | id   : String → Term
  | num  : Nat → Term
  | bin  : String → Term → Term → Term
  /-- Prefix: `¬`, unary `−`, `ℙ`, `⋃`. -/
  | pre  : String → Term → Term
  /-- Postfix: relational inverse `∼`. -/
  | post : String → Term → Term
  /-- Function application `f(x)`; in Event-B a pair argument covers `f(a, b)`. -/
  | app  : Term → Term → Term
  /-- Relational image `r[s]`. -/
  | img  : Term → Term → Term
  /-- Set extension. `set []` is `∅`. -/
  | set  : List Term → Term
  /-- Binder: `∀`, `∃`, `λ`, `⋂`, `⋃`, and `{pat · body}` set comprehension, whose kind
  is `"{"`. The body of a comprehension or lambda is `bin "∣" pred expr`. -/
  | bind : String → Term → Term → Term
  deriving BEq, Repr, Inhabited

/-- Binding power, and whether the operator associates. Non-associating operators reject
`a ∈ b ∈ c` the way Rodin does, rather than silently bracketing it. -/
structure Level where
  power : Nat
  /-- `none` means non-associative. -/
  assoc : Option Bool := some true
  deriving Repr

private def infixLevel : String → Option Level
  | "," => some { power := 5 }
  | "∣" => some { power := 7, assoc := none }
  | "≔" | ":∈" | ":∣" => some { power := 8, assoc := none }
  | "⇔" => some { power := 10, assoc := none }
  | "⇒" => some { power := 12, assoc := some false }
  | "∨" | "∧" => some { power := 14 }
  | "=" | "≠" | "∈" | "∉" | "⊂" | "⊄" | "⊆" | "⊈" | "<" | "≤" | ">" | "≥" =>
      some { power := 20, assoc := none }
  | "↔" | "" | "" | "" | "⇸" | "→" | "⤔" | "↣" | "⤀" | "↠" | "⤖" =>
      some { power := 30, assoc := some false }
  | "×" => some { power := 40 }
  | "∪" | "∩" | "∖" => some { power := 50 }
  | "◁" | "⩤" | "▷" | "⩥" | "" | "∘" | ";" | "⊗" | "∥" => some { power := 55 }
  | "↦" => some { power := 60 }
  | "‥" => some { power := 65, assoc := none }
  | "+" | "−" => some { power := 70 }
  | "∗" | "÷" | "mod" => some { power := 80 }
  | "^" => some { power := 90, assoc := some false }
  | _ => none

/-- Prefix operators. `ℙ`/`ℙ1` take a parenthesised argument but parse as any other
prefix, and the unary minus binds tighter than every infix operator. -/
private def prefixPower : String → Option Nat
  | "¬" => some 16
  | "−" => some 85
  | "ℙ" | "ℙ1" | "⋂" | "⋃" => some 95
  | _ => none

private def isBinder (s : String) : Bool :=
  s == "∀" || s == "∃" || s == "λ" || s == "⋂" || s == "⋃"

/-- `{a, b, c}` parses as nested commas; the set node wants the elements. -/
partial def flattenCommas : Term → List Term
  | .bin "," a b => flattenCommas a ++ flattenCommas b
  | t => [t]

private structure St where
  toks : Array Tok
  pos  : Nat

private def peek (s : St) : Option Tok := s.toks[s.pos]?

private def expect (s : St) (o : String) : Except String St :=
  match peek s with
  | some (.op x) => if x == o then .ok { s with pos := s.pos + 1 }
                    else .error s!"expected {o}, found {x}"
  | some t => .error s!"expected {o}, found {t.render}"
  | none => .error s!"expected {o}, found end of formula"

mutual

/-- Parse at the given minimum binding power. -/
private partial def parseAt (s : St) (minPower : Nat) : Except String (Term × St) := do
  let (lhs, s) ← parsePrefix s
  loop lhs s
where
  loop (lhs : Term) (s : St) : Except String (Term × St) := do
    match peek s with
    | some (.op o) =>
      match infixLevel o with
      | some lvl =>
        if lvl.power < minPower then .ok (lhs, s) else
          -- Only a right-associative operator lets its right side take another
          -- operator of the same power. A non-associative one must not, or the second
          -- occurrence is swallowed before the check below can reject it, and
          -- `a ∈ b ∈ c` parses as `a ∈ (b ∈ c)` instead of failing.
          let rightMin := match lvl.assoc with
            | some false => lvl.power
            | _ => lvl.power + 1
          let (rhs, s) ← parseAt { s with pos := s.pos + 1 } rightMin
          let node := Term.bin o lhs rhs
          if lvl.assoc.isNone then
            match peek s with
            | some (.op o') =>
              if (infixLevel o').any (fun l => l.power == lvl.power) then
                .error s!"operator {o} is not associative"
              else loop node s
            | _ => loop node s
          else loop node s
      | none => .ok (lhs, s)
    | _ => .ok (lhs, s)

private partial def parsePrefix (s : St) : Except String (Term × St) := do
  match peek s with
  | none => .error "unexpected end of formula"
  | some (.num n) => parsePostfix (.num n) { s with pos := s.pos + 1 }
  | some (.id name) => parsePostfix (.id name) { s with pos := s.pos + 1 }
  | some (.op o) =>
    let s := { s with pos := s.pos + 1 }
    if isBinder o then
      -- The pattern runs up to `·`; comma and `↦` inside it are ordinary operators, so
      -- `∀a1,a2·P` and `λx↦y·P∣E` need no special cases.
      let (pat, s) ← parseAt s 5
      let s ← expect s "·"
      let (body, s) ← parseAt s 0
      .ok (.bind o pat body, s)
    else if o == "(" then
      let (inner, s) ← parseAt s 0
      let s ← expect s ")"
      parsePostfix inner s
    else if o == "{" then
      match peek s with
      | some (.op "}") => parsePostfix (.set []) { s with pos := s.pos + 1 }
      | _ =>
        let (inner, s) ← parseAt s 0
        match peek s with
        | some (.op "·") =>
          let (body, s) ← parseAt { s with pos := s.pos + 1 } 0
          let s ← expect s "}"
          parsePostfix (.bind "{" inner body) s
        | _ =>
          let s ← expect s "}"
          parsePostfix (.set (flattenCommas inner)) s
    else if o == "∅" then
      parsePostfix (.set []) s
    else if o == "⊤" || o == "⊥" then
      parsePostfix (.id o) s
    else if o == "ℤ" || o == "ℕ" || o == "ℕ1" then
      parsePostfix (.id o) s
    else
      match prefixPower o with
      | some p => do
        let (arg, s) ← parseAt s p
        parsePostfix (.pre o arg) s
      | none => .error s!"unexpected operator {o}"

/-- Application, image and inverse all bind tighter than any infix operator and chain
freely: `f(x)(y)`, `r[s][t]`, `f∼(x)`. -/
private partial def parsePostfix (t : Term) (s : St) : Except String (Term × St) := do
  match peek s with
  | some (.op "(") =>
    let (arg, s) ← parseAt { s with pos := s.pos + 1 } 0
    let s ← expect s ")"
    parsePostfix (.app t arg) s
  | some (.op "[") =>
    let (arg, s) ← parseAt { s with pos := s.pos + 1 } 0
    let s ← expect s "]"
    parsePostfix (.img t arg) s
  | some (.op "∼") => parsePostfix (.post "∼" t) { s with pos := s.pos + 1 }
  | _ => .ok (t, s)

end

def parseTokens (toks : List Tok) : Except String Term := do
  let (t, s) ← parseAt ⟨toks.toArray, 0⟩ 0
  match peek s with
  | none => .ok t
  | some tok => .error s!"trailing input at {tok.render}"

def parse (source : String) : Except String Term := do
  parseTokens (← lex source)

/-- Fully parenthesised, so the printer states the tree rather than relying on the
reader's memory of the precedence table. Round-tripping is what the P1 gate checks:
`parse (print (parse s)) = parse s`. -/
partial def print : Term → String
  | .id s => s
  | .num n => toString n
  | .bin o a b => "(" ++ print a ++ " " ++ o ++ " " ++ print b ++ ")"
  | .pre o a => "(" ++ o ++ " " ++ print a ++ ")"
  | .post o a => "(" ++ print a ++ o ++ ")"
  | .app f a => print f ++ "(" ++ print a ++ ")"
  | .img r a => print r ++ "[" ++ print a ++ "]"
  | .set ts => "{" ++ String.intercalate ", " (ts.map print) ++ "}"
  | .bind k p b =>
      if k == "{" then "{" ++ print p ++ " · " ++ print b ++ "}"
      else "(" ++ k ++ " " ++ print p ++ " · " ++ print b ++ ")"

/-! Self-checks for the parts the corpus does not pin down: ASCII aliases (Rodin
normalises them away before writing a file) and the precedence decisions. -/

private def sameTree (a b : String) : Bool :=
  match parse a, parse b with
  | .ok x, .ok y => x == y
  | _, _ => false

-- ASCII spellings mean the same thing as the Unicode ones.
#guard sameTree "x : S" "x ∈ S"
#guard sameTree "r <<| s" "r ⩤ s"
#guard sameTree "f +-> g" "f ⇸ g"
#guard sameTree "a |-> b" "a ↦ b"
#guard sameTree "!x · x : S" "∀x · x ∈ S"

-- Longest match: `<<:` is one operator, not `<` then `<:`.
#guard sameTree "a <<: b" "a ⊂ b"
-- A word alias must not eat the head of an identifier.
#guard (parse "order = 1").isOk
#guard (parse "modulus = 1").isOk

-- Precedence: application and image bind tightest, `↦` above `∈`, `∧` above `⇒`.
#guard sameTree "f(x) ∈ S" "(f(x)) ∈ S"
#guard sameTree "a ↦ b ∈ r" "(a ↦ b) ∈ r"
#guard sameTree "p ∧ q ⇒ r" "(p ∧ q) ⇒ r"
#guard sameTree "a + b ∗ c" "a + (b ∗ c)"
#guard sameTree "r[s] ∪ t" "(r[s]) ∪ t"

-- Binders take a comma-separated pattern, and comprehension keeps predicate and
-- expression apart.
#guard (parse "∀a1,a2 · a1 ∈ S ∧ a2 ∈ S ⇒ a1 = a2").isOk
#guard (parse "{x · x ∈ S ∣ x + 1}").isOk
#guard (parse "λx ↦ y · x ∈ ℤ ∧ y ∈ ℤ ∣ x + y").isOk

-- Rejections: an unbalanced bracket and a chained relational operator.
#guard !(parse "f(x").isOk
#guard !(parse "a ∈ b ∈ c").isOk

end EventB.Formula
