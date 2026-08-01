/-
Type inference for Event-B, by unification.

Event-B separates predicates from expressions: a predicate has no type at all, while an
expression does. `Formula.Parse` deliberately keeps one syntax tree, so the split is
made here, where it belongs, by two mutually recursive judgements.

Inference is what makes the `.bpo` gate possible. Rodin recorded the type it inferred
for every identifier; nothing in a `.bum` states those types, so reproducing them means
reproducing the static checker rather than reading an answer off the file.
-/

import EventB.Formula.Parse
import EventB.Theory
import EventB.Typing.Type

namespace EventB.Typing

open EventB.Formula

structure St where
  /-- Indexed by metavariable; `none` until unified. -/
  subst : Array (Option Ty) := #[]
  env   : List (String × Ty) := []
  /-- The native prelude plus any user theories visible to this check. -/
  theory : Theory.Env := Theory.empty
  /-- Theory names imported by the component being checked. -/
  theoryRoots : List String := []
  /-- Event parameters, which leave `env` when their event ends but are still recorded
  in the `.bpo` and so must survive to read-back. -/
  params : List (String × Ty) := []

abbrev M := StateT St (Except String)

def fresh : M Ty := do
  let s ← get
  set { s with subst := s.subst.push none }
  return .mvar s.subst.size

/-- Follow the substitution to the outermost non-variable.

Following a chain of metavariables terminates because every link points to a
strictly lower index: `unify` always assigns the higher of two metavariables to the
lower. That makes the index itself the decreasing measure, so this needs no fuel and,
more usefully, the substitution cannot contain a cycle for it to fall into. -/
def resolve (t : Ty) : M Ty := do
  match t with
  | .mvar n =>
    match (← get).subst[n]? with
    | some (some (.mvar m)) => if m < n then resolve (.mvar m) else return .mvar m
    | some (some u) => return u
    | _ => return t
  | _ => return t
termination_by
  match t with
  | .mvar n => n
  | _ => 0
decreasing_by simp_all

/-- Total size of everything the substitution holds. The fully resolved form of any
type is built from the argument plus what the substitution can splice into it, so this
plus the argument's own size bounds the number of nodes the traversals below visit. -/
def substWeight : M Nat := do
  return ((← get).subst.foldl (fun acc e => acc + (e.map Ty.size).getD 1) 0)

/-- Follow the substitution everywhere, for read-back.

Unlike `resolve`, this recurses on the *result* of a lookup, which can be larger than
its argument, so there is no structural measure. `fuel` is the bound argued above; the
public `zonk` seeds it, and running out would mean the substitution grew during the
traversal, which it cannot. -/
def zonkAux : Nat → Ty → M Ty
  | 0, t => return t
  | fuel + 1, t => do
    match ← resolve t with
    | .pow a => return .pow (← zonkAux fuel a)
    | .prod a b => return .prod (← zonkAux fuel a) (← zonkAux fuel b)
    | t => return t

def zonk (t : Ty) : M Ty := do zonkAux ((← substWeight) + t.size + 1) t

def occursAux : Nat → Nat → Ty → M Bool
  | 0, _, _ => return false
  | fuel + 1, n, t => do
    match ← resolve t with
    | .mvar m => return m == n
    | .pow a => occursAux fuel n a
    | .prod a b => return (← occursAux fuel n a) || (← occursAux fuel n b)
    | _ => return false

def occurs (n : Nat) (t : Ty) : M Bool := do
  occursAux ((← substWeight) + t.size + 1) n t

def unifyAux : Nat → Ty → Ty → M Unit
  | 0, _, _ => return ()
  | fuel + 1, a, b => do
  match ← resolve a, ← resolve b with
  -- Always point the higher metavariable at the lower, which is what lets `resolve`
  -- terminate on the index and rules out a cyclic substitution by construction.
  | .mvar n, .mvar m =>
      if n == m then return ()
      else if n < m then assign m (.mvar n) else assign n (.mvar m)
  | .mvar n, t | t, .mvar n =>
      if ← occurs n t then throw s!"occurs check: ?{n} in {t.print}" else assign n t
  | .int, .int | .bool, .bool => return ()
  | .given x, .given y =>
      if x == y then return () else throw s!"cannot unify {x} with {y}"
  | .pow x, .pow y => unifyAux fuel x y
  | .prod x y, .prod u v => do unifyAux fuel x u; unifyAux fuel y v
  | x, y => throw s!"cannot unify {x.print} with {y.print}"
where
  assign (n : Nat) (t : Ty) : M Unit := do
    modify fun s => { s with subst := s.subst.set! n (some t) }

def unify (a b : Ty) : M Unit := do
  unifyAux ((← substWeight) + a.size + b.size + 1) a b

def lookup? (name : String) : M (Option Ty) := do
  return ((← get).env.find? (fun p => p.1 == name)).map (·.2)

def bind (name : String) (t : Ty) : M Unit :=
  modify fun s => { s with env := (name, t) :: s.env }

/-- A relation `ℙ(A×B)`, returning the two sides. -/
private def asRelation (t : Ty) : M (Ty × Ty) := do
  let a ← fresh
  let b ← fresh
  unify t (.pow (.prod a b))
  return (a, b)

private def asSet (t : Ty) : M Ty := do
  let a ← fresh
  unify t (.pow a)
  return a

/-- Relational predicates: both sides are expressions, and the pair is what constrains
them. `∈` relates an element to a set, `⊆` two sets, the orderings two integers. -/
private def relational : List String :=
  ["=", "≠", "∈", "∉", "⊂", "⊄", "⊆", "⊈", "<", "≤", ">", "≥"]

private def connectives : List String := ["⇔", "⇒", "∧", "∨"]

/-- Operators that build a set from two sets of the same type. -/
private def setBinary : List String := ["∪", "∩", "∖"]

/-- Relation and function arrows, all `ℙ(A) × ℙ(B) → ℙ(ℙ(A×B))`. -/
private def arrows : List String :=
  ["↔", "", "", "", "⇸", "→", "⤔", "↣", "⤀", "↠", "⤖"]

/-- Domain and range restriction: `◁ ⩤` take a set on the left, `▷ ⩥` on the right. -/
private def domRestrict : List String := ["◁", "⩤"]
private def ranRestrict : List String := ["▷", "⩥"]

private theorem termSizePos (t : Term) : 1 ≤ sizeOf t := by
  cases t <;> simp +arith [Term.id.sizeOf_spec, Term.num.sizeOf_spec,
    Term.bin.sizeOf_spec, Term.pre.sizeOf_spec, Term.post.sizeOf_spec,
    Term.app.sizeOf_spec, Term.img.sizeOf_spec, Term.set.sizeOf_spec,
    Term.bind.sizeOf_spec]

mutual

/-- Predicates have no type; the judgement is that the formula is well-formed. -/
def checkPred (t : Term) : M Unit := do
  match t with
  | .id "⊤" | .id "⊥" => return ()
  | .pre "¬" p => checkPred p
  | .bind k pat body =>
      if k == "∀" || k == "∃" then do
        let saved := (← get).env
        bindPattern pat
        checkPred body
        modify fun s => { s with env := saved }
      else throw s!"binder {k} is not a predicate"
  | .bin o a b =>
      if connectives.contains o then do checkPred a; checkPred b
      else if o == "∈" || o == "∉" then do
        let ta ← inferExpr a
        let tb ← inferExpr b
        unify tb (.pow ta)
      else if o == "⊆" || o == "⊈" || o == "⊂" || o == "⊄" then do
        let ta ← inferExpr a
        let tb ← inferExpr b
        let _ ← asSet ta
        unify ta tb
      else if o == "=" || o == "≠" then do
        unify (← inferExpr a) (← inferExpr b)
      else if o == "<" || o == "≤" || o == ">" || o == "≥" then do
        unify (← inferExpr a) .int
        unify (← inferExpr b) .int
      else if o == "≔" then do
        unify (← inferExpr a) (← inferExpr b)
      else if o == ":∈" then do
        unify (.pow (← inferExpr a)) (← inferExpr b)
      else if o == ":∣" then do
        -- Becomes-such-that: the right side is a predicate over primed variables, which
        -- P2 does not model yet. The left side still has to typecheck.
        let _ ← inferExpr a
        return ()
      else throw s!"not a predicate operator: {o}"
  | .app (.id "finite") s => do let _ ← asSet (← inferExpr s)
  | .app (.id "partition") args => do
      -- `partition(S, A, B, ...)`: every argument is a set of the same type.
      let ts ← inferCommaList args
      match ts with
      | [] => throw "partition needs arguments"
      | t :: rest => do
          let _ ← asSet t
          rest.forM (unify t)
  | .id name => do
      -- A bare identifier can be a BOOL-valued predicate only via `bool`, so anything
      -- else here is a use of an undeclared predicate.
      throw s!"not a predicate: {name}"
  | t => throw s!"not a predicate: {Formula.print t}"

termination_by sizeOf t
decreasing_by
  all_goals simp +arith [Term.id.sizeOf_spec, Term.bin.sizeOf_spec, Term.pre.sizeOf_spec,
    Term.app.sizeOf_spec, Term.bind.sizeOf_spec]

/-- The arguments of a comma-separated application, typed left to right. Walking the
comma spine here rather than calling `flattenCommas` keeps the recursion structural:
the results of `flattenCommas` are subterms, but nothing in its type says so. -/
def inferCommaList : Term → M (List Ty)
  | .bin "," a b => do return (← inferCommaList a) ++ (← inferCommaList b)
  | t => do return [← inferExpr t]

termination_by t => sizeOf t + 1
decreasing_by
  all_goals simp +arith [Term.bin.sizeOf_spec]

/-- Bind every identifier in a binder pattern to a fresh type. -/
def bindPattern (t : Term) : M Unit := do
  match t with
  | .id n => do bind n (← fresh)
  | .bin "," a b | .bin "↦" a b => do bindPattern a; bindPattern b
  | t => throw s!"not a binder pattern: {Formula.print t}"

termination_by sizeOf t
decreasing_by
  all_goals simp +arith [Term.bin.sizeOf_spec]

/-- The type of a binder pattern, once its identifiers are bound. -/
def patternType (t : Term) : M Ty := do
  match t with
  | .id n =>
    match ← lookup? n with
    | some ty => return ty
    | none => throw s!"unbound {n}"
  | .bin "↦" a b => return .prod (← patternType a) (← patternType b)
  | t => throw s!"not a binder pattern: {Formula.print t}"

termination_by sizeOf t
decreasing_by
  all_goals simp +arith [Term.bin.sizeOf_spec]

def inferExpr (t : Term) : M Ty := do
  match t with
  | .num _ => return .int
  | .id n =>
    match Theory.typeIn? (← get).theory (← get).theoryRoots n with
    | some ty => return ty
    | none =>
      match ← lookup? n with
      | some ty => return ty
      | none => throw s!"unbound identifier {n}"
  | .set [] => do return .pow (← fresh)
  | .set ts => do
      let ty ← fresh
      ts.attach.forM fun e => do unify (← inferExpr e.1) ty
      return .pow ty
  | .pre "−" e => do unify (← inferExpr e) .int; return .int
  | .pre "ℙ" e | .pre "ℙ1" e => do return .pow (← inferExpr e)
  | .pre "⋃" e | .pre "⋂" e => do
      let inner ← asSet (← inferExpr e)
      let _ ← asSet inner
      return inner
  | .post "∼" e => do
      let (a, b) ← asRelation (← inferExpr e)
      return .pow (.prod b a)
  | .img r s => do
      let (a, b) ← asRelation (← inferExpr r)
      unify (← inferExpr s) (.pow a)
      return .pow b
  | .app f a => inferApp f a
  | .bind k pat body => inferBinder k pat body
  | .bin o a b => inferBin o a b
  | t => throw s!"not an expression: {Formula.print t}"

termination_by sizeOf t
decreasing_by
  · simp_wf
    have h := List.sizeOf_lt_of_mem e.property
    omega
  all_goals simp +arith [Term.pre.sizeOf_spec, Term.post.sizeOf_spec,
    Term.img.sizeOf_spec, Term.app.sizeOf_spec, Term.bind.sizeOf_spec,
    Term.bin.sizeOf_spec]

/-- Function-shaped keywords are ordinary identifiers in the syntax tree, so their typing
rules live here rather than in the lexer. -/
def inferApp (f a : Term) : M Ty := do
  match f with
  | .id "card" => do let _ ← asSet (← inferExpr a); return .int
  | .id "min" | .id "max" => do unify (← inferExpr a) (.pow .int); return .int
  | .id "dom" => do let (x, _) ← asRelation (← inferExpr a); return .pow x
  | .id "ran" => do let (_, y) ← asRelation (← inferExpr a); return .pow y
  | .id "bool" => do checkPred a; return .bool
  | .id "union" | .id "inter" => do
      let inner ← asSet (← inferExpr a)
      let _ ← asSet inner
      return inner
  | .id "succ" | .id "pred" => do unify (← inferExpr a) .int; return .int
  | .id "prj1" => do let (x, _) ← asRelation (← inferExpr a); return .pow x
  | .id "prj2" => do let (_, y) ← asRelation (← inferExpr a); return .pow y
  | .id "id" => do let s ← asSet (← inferExpr a); return .pow (.prod s s)
  | f' => do
      -- Ordinary function application: `f` is a relation and `a` an element of its
      -- domain, which is also how `f(a, b)` works, the argument being a pair.
      let (x, y) ← asRelation (← inferExpr f')
      unify (← inferExpr a) x
      return y

termination_by sizeOf f + sizeOf a
decreasing_by
  all_goals simp_all +arith [termSizePos, Term.id.sizeOf_spec]

def inferBinder (k : String) (pat body : Term) : M Ty := do
  let saved := (← get).env
  bindPattern pat
  let result ← do
    match k, body with
    | "λ", .bin "∣" p e => do
        checkPred p
        return .pow (.prod (← patternType pat) (← inferExpr e))
    | "{", .bin "∣" p e => do
        checkPred p
        return .pow (← inferExpr e)
    | "{", p => do
        -- `{x · P}` with no expression part means the bound variables themselves.
        checkPred p
        return .pow (← patternType pat)
    | "⋃", .bin "∣" p e | "⋂", .bin "∣" p e => do
        checkPred p
        let t ← inferExpr e
        let _ ← asSet t
        return t
    | k, _ => throw s!"binder {k} is not an expression"
  modify fun s => { s with env := saved }
  return result

termination_by sizeOf pat + sizeOf body
decreasing_by
  all_goals simp +arith [termSizePos, Term.bin.sizeOf_spec]

def inferBin (o : String) (a b : Term) : M Ty := do
  if o == "↦" then
    return .prod (← inferExpr a) (← inferExpr b)
  else if setBinary.contains o then do
    let ta ← inferExpr a
    let _ ← asSet ta
    unify ta (← inferExpr b)
    return ta
  else if o == "×" then do
    let x ← asSet (← inferExpr a)
    let y ← asSet (← inferExpr b)
    return .pow (.prod x y)
  else if arrows.contains o then do
    let x ← asSet (← inferExpr a)
    let y ← asSet (← inferExpr b)
    return .pow (.pow (.prod x y))
  else if o == "+" || o == "−" || o == "∗" || o == "÷" || o == "mod" || o == "^" then do
    unify (← inferExpr a) .int
    unify (← inferExpr b) .int
    return .int
  else if o == "‥" then do
    unify (← inferExpr a) .int
    unify (← inferExpr b) .int
    return .pow .int
  else if domRestrict.contains o then do
    let tb ← inferExpr b
    let (x, _) ← asRelation tb
    unify (← inferExpr a) (.pow x)
    return tb
  else if ranRestrict.contains o then do
    let ta ← inferExpr a
    let (_, y) ← asRelation ta
    unify (← inferExpr b) (.pow y)
    return ta
  else if o == "" then do
    let ta ← inferExpr a
    unify ta (← inferExpr b)
    let _ ← asRelation ta
    return ta
  else if o == "∘" || o == ";" then do
    -- `p ; q` composes left to right, `q ∘ p` right to left.
    let (x, y) ← asRelation (← inferExpr a)
    let (u, v) ← asRelation (← inferExpr b)
    if o == ";" then do unify y u; return .pow (.prod x v)
    else do unify v x; return .pow (.prod u y)
  else if o == "⊗" then do
    let (x, y) ← asRelation (← inferExpr a)
    let (u, v) ← asRelation (← inferExpr b)
    unify x u
    return .pow (.prod x (.prod y v))
  else if o == "∥" then do
    let (x, y) ← asRelation (← inferExpr a)
    let (u, v) ← asRelation (← inferExpr b)
    return .pow (.prod (.prod x u) (.prod y v))
  else if relational.contains o || connectives.contains o then
    throw s!"predicate operator {o} used as an expression"
  else
    throw s!"unknown operator {o}"
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp +arith [termSizePos]

end

end EventB.Typing
