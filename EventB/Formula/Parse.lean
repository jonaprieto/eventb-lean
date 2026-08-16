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
  deriving Repr, Inhabited

mutual

  def termBeq : Term → Term → Bool
    | .id left, .id right => left == right
    | .num left, .num right => left == right
    | .bin leftOp left₁ left₂, .bin rightOp right₁ right₂ =>
        leftOp == rightOp && termBeq left₁ right₁ && termBeq left₂ right₂
    | .pre leftOp left, .pre rightOp right
    | .post leftOp left, .post rightOp right => leftOp == rightOp && termBeq left right
    | .app leftFunction leftArgument, .app rightFunction rightArgument
    | .img leftFunction leftArgument, .img rightFunction rightArgument =>
        termBeq leftFunction rightFunction && termBeq leftArgument rightArgument
    | .set left, .set right => termListBeq left right
    | .bind leftKind leftBinder leftBody, .bind rightKind rightBinder rightBody =>
        leftKind == rightKind && termBeq leftBinder rightBinder && termBeq leftBody rightBody
    | _, _ => false

  def termListBeq : List Term → List Term → Bool
    | [], [] => true
    | left :: lefts, right :: rights => termBeq left right && termListBeq lefts rights
    | _, _ => false

end

instance : BEq Term := ⟨termBeq⟩

private theorem congrArg₂' {α β γ : Type} (f : α → β → γ)
    {left left' : α} {right right' : β}
    (leftEq : left = left') (rightEq : right = right') :
    f left right = f left' right' := by
  cases leftEq
  cases rightEq
  rfl

theorem Term.eq_of_beq {left right : Term} (equal : left == right) : left = right := by
  change termBeq left right = true at equal
  exact (Term.rec
    (motive_1 := fun left => ∀ right, termBeq left right = true → left = right)
    (motive_2 := fun left => ∀ right, termListBeq left right = true → left = right)
    (id := fun name right equal => by
      cases right with
      | id other => simp [termBeq] at equal; subst other; rfl
      | num | bin | pre | post | app | img | set | bind => simp [termBeq] at equal)
    (num := fun value right equal => by
      cases right with
      | num other => simp [termBeq] at equal; subst other; rfl
      | id | bin | pre | post | app | img | set | bind => simp [termBeq] at equal)
    (bin := fun op left₁ right₁ ihLeft ihRight right equal => by
      cases right with
      | bin otherOp otherLeft otherRight =>
          simp [termBeq] at equal
          rcases equal with ⟨⟨opEq, leftEq⟩, rightEq⟩
          subst otherOp
          exact congrArg₂' (Term.bin op) (ihLeft otherLeft leftEq) (ihRight otherRight rightEq)
      | id | num | pre | post | app | img | set | bind => simp [termBeq] at equal)
    (pre := fun op value ih right equal => by
      cases right with
      | pre otherOp otherValue =>
          simp [termBeq] at equal
          rcases equal with ⟨opEq, valueEq⟩
          subst otherOp
          exact congrArg (Term.pre op) (ih otherValue valueEq)
      | id | num | bin | post | app | img | set | bind => simp [termBeq] at equal)
    (post := fun op value ih right equal => by
      cases right with
      | post otherOp otherValue =>
          simp [termBeq] at equal
          rcases equal with ⟨opEq, valueEq⟩
          subst otherOp
          exact congrArg (Term.post op) (ih otherValue valueEq)
      | id | num | bin | pre | app | img | set | bind => simp [termBeq] at equal)
    (app := fun function argument ihFunction ihArgument right equal => by
      cases right with
      | app otherFunction otherArgument =>
          simp [termBeq] at equal
          exact congrArg₂' Term.app (ihFunction otherFunction equal.1)
            (ihArgument otherArgument equal.2)
      | id | num | bin | pre | post | img | set | bind => simp [termBeq] at equal)
    (img := fun relation argument ihRelation ihArgument right equal => by
      cases right with
      | img otherRelation otherArgument =>
          simp [termBeq] at equal
          exact congrArg₂' Term.img (ihRelation otherRelation equal.1)
            (ihArgument otherArgument equal.2)
      | id | num | bin | pre | post | app | set | bind => simp [termBeq] at equal)
    (set := fun values ih right equal => by
      cases right with
      | set otherValues => exact congrArg Term.set (ih otherValues equal)
      | id | num | bin | pre | post | app | img | bind => simp [termBeq] at equal)
    (bind := fun quantifier binder body ihBinder ihBody right equal => by
      cases right with
      | bind otherQuantifier otherBinder otherBody =>
          simp [termBeq] at equal
          rcases equal with ⟨⟨quantifierEq, binderEq⟩, bodyEq⟩
          subst otherQuantifier
          exact congrArg₂' (Term.bind quantifier)
            (ihBinder otherBinder binderEq) (ihBody otherBody bodyEq)
      | id | num | bin | pre | post | app | img | set => simp [termBeq] at equal)
    (nil := fun right equal => by
      cases right with
      | nil => rfl
      | cons => simp [termListBeq] at equal)
    (cons := fun head tail ihHead ihTail right equal => by
      cases right with
      | nil => simp [termListBeq] at equal
      | cons otherHead otherTail =>
          simp [termListBeq] at equal
          exact congrArg₂' List.cons (ihHead otherHead equal.1) (ihTail otherTail equal.2))
    left) right equal

theorem Term.beq_self (term : Term) : termBeq term term = true := by
  exact Term.rec
    (motive_1 := fun term => termBeq term term = true)
    (motive_2 := fun terms => termListBeq terms terms = true)
    (id := fun _ => by simp [termBeq])
    (num := fun _ => by simp [termBeq])
    (bin := fun _ _ _ ihLeft ihRight => by simp [termBeq, ihLeft, ihRight])
    (pre := fun _ _ ih => by simp [termBeq, ih])
    (post := fun _ _ ih => by simp [termBeq, ih])
    (app := fun _ _ ihFunction ihArgument => by simp [termBeq, ihFunction, ihArgument])
    (img := fun _ _ ihRelation ihArgument => by simp [termBeq, ihRelation, ihArgument])
    (set := fun _ ih => ih)
    (bind := fun _ _ _ ihBinder ihBody => by simp [termBeq, ihBinder, ihBody])
    (nil := by rfl)
    (cons := fun _ _ ihHead ihTail => by simp [termListBeq, ihHead, ihTail])
    term

instance : LawfulBEq Term where
  rfl := Term.beq_self _
  eq_of_beq := Term.eq_of_beq

instance : DecidableEq Term := instDecidableEqOfLawfulBEq

/-- Binding power, and whether the operator associates. Non-associating operators reject
`a ∈ b ∈ c` the way Rodin does, rather than silently bracketing it. -/
structure Level where
  power : Nat
  /-- `none` means non-associative. -/
  assoc : Option Bool := some true
  deriving Repr

private def infixLevel : String → Option Level
  -- Parallel assignment lists must bind more tightly than `≔`: `a,b ≔ x,y`
  -- is one assignment with comma-separated sides, not a comma-rooted predicate.
  | "," => some { power := 9 }
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
  -- Product binds tighter than maplet: `a ↦ b × c` means `a ↦ (b × c)`.
  | "↦" => some { power := 35 }
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

private def hasRemainingOperator (s : St) (operator : String) : Bool :=
  (s.toks.toList.drop s.pos).any fun token =>
    match token with
    | .op value => value == operator
    | _ => false

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
    if isBinder o &&
        (o != "⋃" && o != "⋂" || hasRemainingOperator s "·") then
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

private def parseTokensText (toks : List Tok) : Except String Term := do
  let arr := toks.toArray
  -- Consuming one token can descend `parseAt -> parsePrefix -> parsePostfix` and come
  -- back through `parseInfix`, and each of those decrements, so the budget is a small
  -- constant per token rather than one. Seeding it at the token count silently rejected
  -- long predicates with "parser made no progress".
  let (t, s) ← parseAt (4 * arr.size + 8) ⟨arr, 0⟩ 0
  match peek s with
  | none => .ok t
  | some tok => .error s!"trailing input at {tok.render}"

def parseTokens (toks : List Tok) : Except EventB.Error Term :=
  (parseTokensText toks).mapError EventB.Error.formula

def parse (source : String) : Except EventB.Error Term := do
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
#guard sameTree "a ↦ b × c" "a ↦ (b × c)"
#guard sameTree "a,b ≔ x,y" "(a,b) ≔ (x,y)"
#guard sameTree "p ∧ q ⇒ r" "(p ∧ q) ⇒ r"
#guard sameTree "a + b ∗ c" "a + (b ∗ c)"
#guard sameTree "r[s] ∪ t" "(r[s]) ∪ t"

-- Binders take a comma-separated pattern, and comprehension keeps predicate and
-- expression apart.
#guard (parse "∀a1,a2 · a1 ∈ S ∧ a2 ∈ S ⇒ a1 = a2").isOk
#guard match parse "⋃S" with
  | .ok term => term == .pre "⋃" (.id "S")
  | .error _ => false
#guard match parse "⋂S" with
  | .ok term => term == .pre "⋂" (.id "S")
  | .error _ => false
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

private def allNames : Term → List String
  | .id n => [n]
  | .num _ => []
  | .bin _ a b => allNames a ++ allNames b
  | .pre _ a | .post _ a => allNames a
  | .app f a | .img f a => allNames f ++ allNames a
  | .set ts => ts.flatMap allNames
  | .bind _ p b => allNames p ++ allNames b

private def freshName (base : String) (used : List String) : Nat → String
  | 0 => base ++ "0"
  | fuel + 1 =>
      if used.contains base then freshName (base ++ "0") used fuel else base

private def makeRenames : List String → List String → List String →
    List (String × String) × List String
  | [], _, used => ([], used)
  | name :: names, conflicts, used =>
      let renamed := if conflicts.contains name then
        freshName name used (used.length + 1)
      else name
      let (rest, finalUsed) := makeRenames names conflicts (renamed :: used)
      ((name, renamed) :: rest, finalUsed)

private def renameBound (mapping : List (String × String)) : Term → Term
  | .id name => .id (mapping.find? (fun pair => pair.1 == name) |>.map (·.2) |>.getD name)
  | .num value => .num value
  | .bin op a b => .bin op (renameBound mapping a) (renameBound mapping b)
  | .pre op a => .pre op (renameBound mapping a)
  | .post op a => .post op (renameBound mapping a)
  | .app f a => .app (renameBound mapping f) (renameBound mapping a)
  | .img r a => .img (renameBound mapping r) (renameBound mapping a)
  | .set ts => .set (ts.map (renameBound mapping))
  | .bind kind pattern body =>
      let shadowed := patternNames pattern
      .bind kind (renameBound mapping pattern)
        (renameBound (mapping.filter (fun pair => !shadowed.contains pair.1)) body)

mutual

private def termFuel : Term → Nat
  | .id _ | .num _ => 1
  | .bin _ a b => 1 + termFuel a + termFuel b
  | .pre _ a | .post _ a => 1 + termFuel a
  | .app f a | .img f a => 1 + termFuel f + termFuel a
  | .set ts => 1 + termFuelList ts
  | .bind _ p b => 1 + termFuel p + termFuel b

private def termFuelList : List Term → Nat
  | [] => 0
  | t :: ts => termFuel t + termFuelList ts

end

mutual

/-- Fuelled implementation of simultaneous substitution. Fuel lets the binder case
alpha-rename before descending without weakening termination to a partial function. -/
private def substFuel : Nat → List (String × Term) → Term → Term
  | 0, _, term => term
  | _fuel + 1, σ, .id n =>
      match σ.find? (fun p => p.1 == n) with
      | some (_, t) => t
      | none => .id n
  | _fuel + 1, _, .num n => .num n
  | fuel + 1, σ, .bin o a b => .bin o (substFuel fuel σ a) (substFuel fuel σ b)
  | fuel + 1, σ, .pre o a => .pre o (substFuel fuel σ a)
  | fuel + 1, σ, .post o a => .post o (substFuel fuel σ a)
  | fuel + 1, σ, .app f a => .app (substFuel fuel σ f) (substFuel fuel σ a)
  | fuel + 1, σ, .img r a => .img (substFuel fuel σ r) (substFuel fuel σ a)
  | fuel + 1, σ, .set ts => .set (substListFuel fuel σ ts)
  -- A binder captures only the names in its own pattern. Machine variables are free
  -- inside a quantified invariant and must be substituted there, while a replacement
  -- that mentions a bound name first triggers alpha-renaming to avoid capture.
  | fuel + 1, σ, .bind k p b =>
      let bound := patternNames p
      let rhsNames := σ.flatMap (fun (_, term) => allNames term)
      let used := allNames p ++ allNames b ++ rhsNames ++ σ.map (·.1)
      let (renames, _) := makeRenames bound rhsNames used
      let renamedPattern := renameBound renames p
      let renamedBody := renameBound renames b
      let renamedBound := patternNames renamedPattern
      .bind k renamedPattern
        (substFuel fuel (σ.filter (fun q => !renamedBound.contains q.1)) renamedBody)

private def substListFuel : Nat → List (String × Term) → List Term → List Term
  | 0, _, terms => terms
  | _fuel + 1, _, [] => []
  | fuel + 1, σ, term :: terms =>
      substFuel fuel σ term :: substListFuel fuel σ terms

end

/-- Simultaneous substitution. Simultaneous matters: an event assigning `a ≔ b` and
`b ≔ a` swaps them, and capture-avoiding binders preserve the same semantics. -/
def subst (σ : List (String × Term)) (term : Term) : Term :=
  substFuel (termFuel term + 1) σ term

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

/-- Compare formulas modulo the names chosen for bound variables. Rodin alpha-renames
bound identifiers when an event parameter would collide with one; those names carry no
logical content and must not make the P3b statement gate reject the same formula. -/
def alphaEq (left right : Term) : Bool :=
  go left right [] [] 0
where
  lookup (name : String) (env : List (String × Nat)) : Option Nat :=
    env.find? (fun pair => pair.1 == name) |>.map (·.2)

  patternShape : Term → Term → Bool
    | .id _, .id _ => true
    | .bin leftOp a b, .bin rightOp c d =>
        leftOp == rightOp && patternShape a c && patternShape b d
    | _, _ => false

  bindings : List String → Nat → List (String × Nat)
    | [], _ => []
    | name :: names, index => (name, index) :: bindings names (index + 1)

  terms : List Term → List Term → List (String × Nat) → List (String × Nat) → Nat → Bool
    | [], [], _, _, _ => true
    | left :: lefts, right :: rights, leftEnv, rightEnv, next =>
        go left right leftEnv rightEnv next && terms lefts rights leftEnv rightEnv next
    | _, _, _, _, _ => false

  go : Term → Term → List (String × Nat) → List (String × Nat) → Nat → Bool
    | .id leftName, .id rightName, leftEnv, rightEnv, _ =>
        match lookup leftName leftEnv, lookup rightName rightEnv with
        | some leftIndex, some rightIndex => leftIndex == rightIndex
        | none, none => leftName == rightName
        | _, _ => false
    | .num leftNumber, .num rightNumber, _, _, _ => leftNumber == rightNumber
    | .bin leftOp leftA leftB, .bin rightOp rightA rightB, leftEnv, rightEnv, next =>
        leftOp == rightOp && go leftA rightA leftEnv rightEnv next &&
          go leftB rightB leftEnv rightEnv next
    | .pre leftOp leftTerm, .pre rightOp rightTerm, leftEnv, rightEnv, next =>
        leftOp == rightOp && go leftTerm rightTerm leftEnv rightEnv next
    | .post leftOp leftTerm, .post rightOp rightTerm, leftEnv, rightEnv, next =>
        leftOp == rightOp && go leftTerm rightTerm leftEnv rightEnv next
    | .app leftFunction leftArgument, .app rightFunction rightArgument,
        leftEnv, rightEnv, next =>
        go leftFunction rightFunction leftEnv rightEnv next &&
          go leftArgument rightArgument leftEnv rightEnv next
    | .img leftRelation leftArgument, .img rightRelation rightArgument,
        leftEnv, rightEnv, next =>
        go leftRelation rightRelation leftEnv rightEnv next &&
          go leftArgument rightArgument leftEnv rightEnv next
    | .set leftTerms, .set rightTerms, leftEnv, rightEnv, next =>
        terms leftTerms rightTerms leftEnv rightEnv next
    | .bind leftKind leftPattern leftBody, .bind rightKind rightPattern rightBody,
        leftEnv, rightEnv, next =>
        let leftNames := patternNames leftPattern
        let rightNames := patternNames rightPattern
        let leftBindings := bindings leftNames next
        let rightBindings := bindings rightNames next
        leftKind == rightKind && patternShape leftPattern rightPattern &&
          leftNames.length == rightNames.length &&
          go leftBody rightBody
            (leftBindings ++ leftEnv.filter (fun pair => !leftNames.contains pair.1))
            (rightBindings ++ rightEnv.filter (fun pair => !rightNames.contains pair.1))
            (next + leftNames.length)
    | _, _, _, _, _ => false

/-! Self-checks for substitution and ascription stripping. -/

private def parse! (s : String) : Term := (parse s).toOption.getD (.id "?")

-- The shape every INV obligation has: the invariant with assigned variables replaced.
#guard subst [("held_airplanes", parse! "held_airplanes ∪ {airplane}")]
    (parse! "held_airplanes ⊆ dom(landing_sequence)")
  == parse! "held_airplanes ∪ {airplane} ⊆ dom(landing_sequence)"

-- Simultaneous, not sequential: a swap must not collapse.
#guard subst [("a", .id "b"), ("b", .id "a")] (parse! "a ∪ b") == parse! "b ∪ a"

-- Substitution must rename a binder when a replacement would capture it.
#guard subst [("x", .id "tr")] (parse! "∀tr · tr = x")
  == parse! "∀tr0 · tr0 = tr"

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
#guard alphaEq (parse! "∀x · x ∈ S") (parse! "∀y · y ∈ S")
#guard !alphaEq (parse! "∀x · x ∈ S") (parse! "∀y · y ∈ T")
#guard alphaEq (parse! "∀x · x ∈ S ⇒ ∃y · y = x")
  (parse! "∀a · a ∈ S ⇒ ∃b · b = a")
#guard alphaEq (parse! "f = λx · x ∈ S ∣ x") (parse! "f = λy · y ∈ S ∣ y")
#guard alphaEq (parse! "x ∈ S ∧ y = f(x)") (parse! "x ∈ S ∧ y = f(x)")
#guard alphaEq (stripAscriptions (parse! "∀a1⦂ℤ,a2⦂ℤ · a1 ∈ S ∧ a2 ∈ S ⇒ a1 = a2"))
  (stripAscriptions (parse! "∀a1⦂ℤ,a2⦂ℤ · a1 ∈ S ∧ a2 ∈ S ⇒ a1 = a2"))

end EventB.Formula
