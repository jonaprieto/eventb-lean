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
  -- Binds tighter than `↦` and `,` so that `∀x⦂ℤ,y⦂ℤ·P` and `λx⦂ℤ ↦ y⦂ℤ·E` group the
  -- ascription with its own variable.
  | "⦂" => some { power := 75, assoc := none }
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
def flattenCommas : Term → List Term
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
-- Every recursive call happens after at least one token has been consumed, so the
-- parser terminates; but `St` carries the position in a field, and nothing in the type
-- says the position advances. `fuel` states the bound: seeded at the token count, it
-- can only run out if some branch consumed nothing. Same obligation as in `Lex`, and
-- the same note applies: grip's graded parsers discharge it by construction.
private def parseAt : Nat → St → Nat → Except String (Term × St)
  | 0, _, _ => .error "parser made no progress"
  | fuel + 1, s, minPower => do
      let (lhs, s) ← parsePrefix fuel s
      parseInfix fuel minPower lhs s
termination_by fuel _ _ => fuel

/-- The operator loop of `parseAt`, split out because it needs the decremented fuel and
a `where` clause cannot see it. -/
private def parseInfix : Nat → Nat → Term → St → Except String (Term × St)
  | 0, _, lhs, s => .ok (lhs, s)
  | fuel + 1, minPower, lhs, s => do
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
          let (rhs, s) ← parseAt fuel { s with pos := s.pos + 1 } rightMin
          let node := Term.bin o lhs rhs
          if lvl.assoc.isNone then
            match peek s with
            | some (.op o') =>
              if (infixLevel o').any (fun l => l.power == lvl.power) then
                .error s!"operator {o} is not associative"
              else parseInfix fuel minPower node s
            | _ => parseInfix fuel minPower node s
          else parseInfix fuel minPower node s
      | none => .ok (lhs, s)
    | _ => .ok (lhs, s)
termination_by fuel _ _ _ => fuel

private def parsePrefix : Nat → St → Except String (Term × St)
  | 0, _ => .error "parser made no progress"
  | fuel + 1, s => do
  match peek s with
  | none => .error "unexpected end of formula"
  | some (.num n) => parsePostfix fuel (.num n) { s with pos := s.pos + 1 }
  | some (.id name) => parsePostfix fuel (.id name) { s with pos := s.pos + 1 }
  | some (.op o) =>
    let s := { s with pos := s.pos + 1 }
    if isBinder o then
      -- The pattern runs up to `·`; comma and `↦` inside it are ordinary operators, so
      -- `∀a1,a2·P` and `λx↦y·P∣E` need no special cases.
      let (pat, s) ← parseAt fuel s 5
      let s ← expect s "·"
      let (body, s) ← parseAt fuel s 0
      .ok (.bind o pat body, s)
    else if o == "(" then
      let (inner, s) ← parseAt fuel s 0
      let s ← expect s ")"
      parsePostfix fuel inner s
    else if o == "{" then
      match peek s with
      | some (.op "}") => parsePostfix fuel (.set []) { s with pos := s.pos + 1 }
      | _ =>
        let (inner, s) ← parseAt fuel s 0
        match peek s with
        | some (.op "·") =>
          let (body, s) ← parseAt fuel { s with pos := s.pos + 1 } 0
          let s ← expect s "}"
          parsePostfix fuel (.bind "{" inner body) s
        | _ =>
          let s ← expect s "}"
          -- `{E ∣ P}` is the short form of `{E · P ∣ E}`, not a set literal whose one
          -- element happens to contain a bar. Parsing it as a literal made the same set
          -- take two different shapes depending on which spelling was used.
          match inner with
          | .bin "∣" expr pred =>
              parsePostfix fuel (.bind "{" expr (.bin "∣" pred expr)) s
          | _ => parsePostfix fuel (.set (flattenCommas inner)) s
    else if o == "∅" then
      parsePostfix fuel (.set []) s
    else if o == "⊤" || o == "⊥" then
      parsePostfix fuel (.id o) s
    else if o == "ℤ" || o == "ℕ" || o == "ℕ1" then
      parsePostfix fuel (.id o) s
    else
      match prefixPower o with
      | some p => do
        let (arg, s) ← parseAt fuel s p
        parsePostfix fuel (.pre o arg) s
      | none => .error s!"unexpected operator {o}"
termination_by fuel _ => fuel

/-- Application, image and inverse all bind tighter than any infix operator and chain
freely: `f(x)(y)`, `r[s][t]`, `f∼(x)`. -/
private def parsePostfix : Nat → Term → St → Except String (Term × St)
  | 0, t, s => .ok (t, s)
  | fuel + 1, t, s => do
  match peek s with
  | some (.op "(") =>
    let (arg, s) ← parseAt fuel { s with pos := s.pos + 1 } 0
    let s ← expect s ")"
    parsePostfix fuel (.app t arg) s
  | some (.op "[") =>
    let (arg, s) ← parseAt fuel { s with pos := s.pos + 1 } 0
    let s ← expect s "]"
    parsePostfix fuel (.img t arg) s
  | some (.op "{") =>
    -- `f{x ↦ y}` directly after a term is Rodin's spelling of functional override,
    -- `f  {x ↦ y}`. A brace in prefix position is still a set literal; only
    -- juxtaposition means override.
    let (arg, s) ← parseAt fuel { s with pos := s.pos + 1 } 0
    let s ← expect s "}"
    parsePostfix fuel (.bin "" t (.set (flattenCommas arg))) s
  | some (.op "∼") => parsePostfix fuel (.post "∼" t) { s with pos := s.pos + 1 }
  | _ => .ok (t, s)
termination_by fuel _ _ => fuel

end

def parseTokens (toks : List Tok) : Except String Term := do
  let arr := toks.toArray
  -- Consuming one token can descend `parseAt -> parsePrefix -> parsePostfix` and come
  -- back through `parseInfix`, and each of those decrements, so the budget is a small
  -- constant per token rather than one. Seeding it at the token count silently rejected
  -- long predicates with "parser made no progress".
  let (t, s) ← parseAt (4 * arr.size + 8) ⟨arr, 0⟩ 0
  match peek s with
  | none => .ok t
  | some tok => .error s!"trailing input at {tok.render}"

def parse (source : String) : Except String Term := do
  parseTokens (← lex source)

/-- Fully parenthesised, so the printer states the tree rather than relying on the
reader's memory of the precedence table. Round-tripping is what the P1 gate checks:
`parse (print (parse s)) = parse s`. -/
def print : Term → String
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
#guard sameTree "x <= 1" "x ≤ 1"
#guard sameTree "S \\ T" "S ∖ T"
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
-- The short form of comprehension denotes the same set as the long one.
#guard sameTree "{x ∣ x ∈ S}" "{x · x ∈ S ∣ x}"
#guard (parse "λx ↦ y · x ∈ ℤ ∧ y ∈ ℤ ∣ x + y").isOk

-- Functional override written by juxtaposition, as Rodin writes it.
#guard sameTree "f{a ↦ b}" "f  {a ↦ b}"
-- A brace not directly after a term is still a set literal.
#guard sameTree "S ∪ {a}" "S ∪ {a}"

-- Rejections: an unbalanced bracket and a chained relational operator.
#guard !(parse "f(x").isOk
#guard !(parse "a ∈ b ∈ c").isOk

/-- The names a binder pattern introduces. Substitution must skip exactly these and
descend past everything else. -/
def patternNames : Term → List String
  | .id n => [n]
  | .bin "⦂" a _ => patternNames a
  | .bin _ a b => patternNames a ++ patternNames b
  | _ => []

mutual

/-- Simultaneous substitution. Simultaneous matters: an event assigning `a ≔ b` and
`b ≔ a` swaps them, and substituting one at a time would not. -/
def subst (σ : List (String × Term)) : Term → Term
  | .id n => match σ.find? (fun p => p.1 == n) with
             | some (_, t) => t
             | none => .id n
  | .num n => .num n
  | .bin o a b => .bin o (subst σ a) (subst σ b)
  | .pre o a => .pre o (subst σ a)
  | .post o a => .post o (subst σ a)
  | .app f a => .app (subst σ f) (subst σ a)
  | .img r a => .img (subst σ r) (subst σ a)
  | .set ts => .set (substList σ ts)
  -- A binder captures only the names in its own pattern. Machine variables are free
  -- inside a quantified invariant and must be substituted there too, which is what
  -- makes `∀a1,a2 · a1 ∈ dom(f) ⇒ ...` become `... dom(∅) ...` after `f ≔ ∅`.
  | .bind k p b =>
      let bound := patternNames p
      .bind k p (subst (σ.filter (fun q => !bound.contains q.1)) b)

def substList (σ : List (String × Term)) : List Term → List Term
  | [] => []
  | t :: ts => subst σ t :: substList σ ts

end

mutual

/-- Drop the type ascriptions Rodin writes into `.bpo` predicates. They carry no logical
content, and a generator has no reason to reproduce them, so comparisons are modulo
ascription. -/
def stripAscriptions : Term → Term
  | .bin "⦂" a _ => stripAscriptions a
  | .bin o a b => .bin o (stripAscriptions a) (stripAscriptions b)
  | .pre o a => .pre o (stripAscriptions a)
  | .post o a => .post o (stripAscriptions a)
  | .app f a => .app (stripAscriptions f) (stripAscriptions a)
  | .img r a => .img (stripAscriptions r) (stripAscriptions a)
  | .set ts => .set (stripList ts)
  | .bind k p b => .bind k (stripAscriptions p) (stripAscriptions b)
  | t => t

def stripList : List Term → List Term
  | [] => []
  | t :: ts => stripAscriptions t :: stripList ts

end

/-! Self-checks for substitution and ascription stripping. -/

private def parse! (s : String) : Term := (parse s).toOption.getD (.id "?")

-- The shape every INV obligation has: the invariant with assigned variables replaced.
#guard subst [("held_airplanes", parse! "held_airplanes ∪ {airplane}")]
    (parse! "held_airplanes ⊆ dom(landing_sequence)")
  == parse! "held_airplanes ∪ {airplane} ⊆ dom(landing_sequence)"

-- Simultaneous, not sequential: a swap must not collapse.
#guard subst [("a", .id "b"), ("b", .id "a")] (parse! "a ∪ b") == parse! "b ∪ a"

-- A name the event does not assign is untouched.
#guard subst [("x", .id "y")] (parse! "z ∈ S") == parse! "z ∈ S"

-- Substitution reaches inside a quantifier: `a1` is bound, `f` is not.
#guard subst [("f", .set [])] (parse! "∀a1 · a1 ∈ dom(f)")
  == parse! "∀a1 · a1 ∈ dom(∅)"

-- But a name the binder captures is shadowed, not replaced.
#guard subst [("a1", .id "q")] (parse! "∀a1 · a1 ∈ S") == parse! "∀a1 · a1 ∈ S"

-- Ascriptions vanish, and nothing else does.
#guard stripAscriptions (parse! "(∅ ⦂ ℙ(AIRPLANES)) ⊆ dom(f)") == parse! "∅ ⊆ dom(f)"
#guard stripAscriptions (parse! "∀x⦂ℤ · x ∈ S") == parse! "∀x · x ∈ S"

end EventB.Formula
