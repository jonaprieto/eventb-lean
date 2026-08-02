/- Minimal proof-term construction for propositions already translated to Lean. -/

import EventB.Trust.Replay

namespace EventB.Prover.Kernel

open Lean Elab Command Meta
open EventB EventB.Embedding EventB.Formula EventB.POG

inductive Rule where
  | exactHypothesis
  | true
  | reflexive
  | contradiction
  deriving BEq, Repr, Inhabited

def Rule.label : Rule → String
  | .exactHypothesis => "exact-hypothesis"
  | .true => "true"
  | .reflexive => "reflexive"
  | .contradiction => "contradiction"

structure Result where
  rule : Option Rule := none
  proof : Option Expr := none
  deriving Inhabited

def Result.discharged (result : Result) : Bool := result.rule.isSome

private def withHypLocals {α : Type} (hypotheses : List Expr)
    (locals : List Expr) (body : List Expr → MetaM α) : MetaM α :=
  match hypotheses with
  | [] => body locals
  | hypothesis :: rest =>
      withLocalDeclD (Name.mkSimple s!"h{locals.length}") hypothesis fun localVar =>
        withHypLocals rest (locals ++ [localVar]) body

private def lambda (locals : List Expr) (body : Expr) : MetaM Expr :=
  mkLambdaFVars locals.toArray body

private def reflexiveProof (goal : Expr) : MetaM (Option Expr) := do
  let goal ← whnf goal
  match goal with
  | .app (.app (.app (.const ``Eq _) _) left) right =>
      if ← isDefEq left right then some <$> mkAppM ``Eq.refl #[left] else pure none
  | _ => pure none

private def ruleProof (pairs : List (Expr × Expr)) (goal : Expr) : MetaM (Option (Rule × Expr)) := do
  for pair in pairs do
    if ← isDefEq pair.1 goal then
      return some (.exactHypothesis, ← lambda (pairs.map (·.2)) pair.2)
  if ← isDefEq goal (mkConst ``True) then
    return some (.true, ← lambda (pairs.map (·.2)) (mkConst ``True.intro))
  if let some proof ← reflexiveProof goal then
    return some (.reflexive, ← lambda (pairs.map (·.2)) proof)
  for pair in pairs do
    if ← isDefEq pair.1 (mkConst ``False) then
      let proof := mkApp (mkApp (mkConst ``False.elim [Level.zero]) goal) pair.2
      return some (.contradiction, ← lambda (pairs.map (·.2)) proof)
  pure none

def prove (context : KernelContext) (obligation : Obligation) : MetaM Result := do
  let goal ← match obligation.goal with
    | some value => Embedding.translatePredicate context value
    | none => throwError s!"obligation `{obligation.name}` has no translated goal"
  let hypotheses ← obligation.hyps.mapM (Embedding.translatePredicate context)
  withHypLocals hypotheses [] fun locals => do
    match ← ruleProof (hypotheses.zip locals) goal with
    | some (rule, proof) => pure { rule := some rule, proof := some proof }
    | none => pure {}

def validate (context : KernelContext) (obligation : Obligation) : MetaM Result := do
  let result ← prove context obligation
  match result.proof with
  | none => pure result
  | some proof =>
      let _ ← Trust.Replay.validateTerm context obligation proof
      pure result

end EventB.Prover.Kernel
