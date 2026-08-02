/-
Small deterministic discharge baseline.

This is intentionally not a theorem prover. It recognizes only proof steps whose
syntax is easy to audit and returns external evidence, which keeps the trust boundary
honest until a kernel proof term or a separately verified backend is available.
-/

import EventB.Trust

namespace EventB.Prover.Local

open EventB EventB.Formula EventB.POG EventB.Trust

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
  evidence : Evidence := .none
  deriving BEq, Repr, Inhabited

def Result.discharged (result : Result) : Bool := result.rule.isSome

private def isReflexive : Term → Bool
  | .bin "=" left right => Formula.alphaEq left right
  | _ => false

private def isFalse : Term → Bool
  | .id "⊥" => true
  | _ => false

private def rule? (obligation : Obligation) : Option Rule := do
  let goal ← obligation.goal
  if goal == .id "⊤" then
    some .true
  else if obligation.hyps.any (Formula.alphaEq goal) then
    some .exactHypothesis
  else if isReflexive goal then
    some .reflexive
  else if isFalse goal && obligation.hyps.any isFalse then
    some .contradiction
  else
    none

def evidence (obligation : Obligation) (rule : Rule) : Evidence :=
  .external "eventb-local" "0" (Trust.fingerprint
    (obligation.canonical ++ "\nrule=" ++ rule.label)) "EventB.Prover.Local"

def prove (obligation : Obligation) : Result :=
  match rule? obligation with
  | some rule => { rule := some rule, evidence := evidence obligation rule }
  | none => {}

def attach (ledger : Ledger) (obligation : Obligation) : Result → Except String Ledger
  | { rule := some _, evidence } => ledger.attach obligation evidence
  | _ => pure ledger

private def trueObligation : Obligation :=
  { component := "Local", name := "true", kind := "THM", goal := some (.id "⊤") }

private def reflexiveObligation : Obligation :=
  { component := "Local", name := "refl", kind := "THM"
    goal := some (.bin "=" (.id "x") (.id "x")) }

#guard (prove trueObligation).discharged
#guard (prove reflexiveObligation).rule == some .reflexive
#guard !(prove { trueObligation with goal := some (.id "missing") }).discharged
#guard match attach (Ledger.ofObligations [trueObligation]) trueObligation
    (prove trueObligation) with
  | .ok ledger => ledger.count .external == 1
  | .error _ => false

end EventB.Prover.Local
