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
  | andIntro
  | implicationIntro
  | hypothesisProjection
  deriving BEq, Repr, Inhabited

def Rule.label : Rule → String
  | .exactHypothesis => "exact-hypothesis"
  | .true => "true"
  | .reflexive => "reflexive"
  | .contradiction => "contradiction"
  | .andIntro => "and-intro"
  | .implicationIntro => "implication-intro"
  | .hypothesisProjection => "hypothesis-projection"

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

private def basicProof (pairs : List (Expr × Expr)) (goal : Expr) :
    MetaM (Option (Rule × Expr)) := do
  for pair in pairs do
    if ← isDefEq pair.1 goal then
      return some (.exactHypothesis, pair.2)
  if ← isDefEq goal (mkConst ``True) then
    return some (.true, mkConst ``True.intro)
  if let some proof ← reflexiveProof goal then
    return some (.reflexive, proof)
  for pair in pairs do
    if ← isDefEq pair.1 (mkConst ``False) then
      let proof := mkApp (mkApp (mkConst ``False.elim [Level.zero]) goal) pair.2
      return some (.contradiction, proof)
  pure none

private def andParts (goal : Expr) : MetaM (Option (Expr × Expr)) := do
  let goal ← whnf goal
  match goal with
  | .app (.app (.const ``And _) left) right => pure (some (left, right))
  | _ => pure none

private def implicationParts (goal : Expr) : MetaM (Option (Expr × Expr)) := do
  let goal ← whnf goal
  match goal with
  | .forallE _ premise body _ => pure (some (premise, body))
  | _ => pure none

private def projection (pairs : List (Expr × Expr)) (goal : Expr) :
    MetaM (Option Expr) := do
  for pair in pairs do
    let hypothesis ← whnf pair.1
    match hypothesis with
    | .app (.app (.const ``And _) left) right =>
        if ← isDefEq left goal then
          return some (← mkAppM ``And.left #[pair.2])
        if ← isDefEq right goal then
          return some (← mkAppM ``And.right #[pair.2])
    | _ => pure ()
  pure none

private def ruleProof : Nat → List (Expr × Expr) → Expr → MetaM (Option (Rule × Expr))
  | 0, pairs, goal => do
      if let some proof ← projection pairs goal then
        pure (some (.hypothesisProjection, proof))
      else
        basicProof pairs goal
  | fuel + 1, pairs, goal => do
      if let some proof ← basicProof pairs goal then
        return some proof
      if let some proof ← projection pairs goal then
        return some (.hypothesisProjection, proof)
      if let some (left, right) ← andParts goal then
        match ← ruleProof fuel pairs left, ← ruleProof fuel pairs right with
        | some (_, leftProof), some (_, rightProof) =>
            let proof ← mkAppM ``And.intro #[leftProof, rightProof]
            pure (some (.andIntro, proof))
        | _, _ => pure none
      else if let some (premise, body) ← implicationParts goal then
        withLocalDeclD `hypothesis premise fun localVar => do
          match ← ruleProof fuel ((premise, localVar) :: pairs)
              (body.instantiate1 localVar) with
          | some (_, proof) =>
              pure (some (.implicationIntro, ← mkLambdaFVars #[localVar] proof))
          | none => pure none
      else
        pure none

def prove (context : KernelContext) (obligation : Obligation) : MetaM Result := do
  let goal ← match obligation.goal with
    | some value => Embedding.translatePredicate context value
    | none => throwError s!"obligation `{obligation.name}` has no translated goal"
  let hypotheses ← obligation.hyps.mapM (Embedding.translatePredicate context)
  withHypLocals hypotheses [] fun locals => do
    match ← ruleProof 8 (hypotheses.zip locals) goal with
    | some (rule, body) =>
        let proof ← lambda locals body
        pure { rule := some rule, proof := some proof }
    | none => pure {}

def validate (context : KernelContext) (obligation : Obligation) : MetaM Result := do
  let result ← prove context obligation
  match result.proof with
  | none => pure result
  | some proof =>
      let _ ← Trust.Replay.validateTerm context obligation proof
      pure result

end EventB.Prover.Kernel
