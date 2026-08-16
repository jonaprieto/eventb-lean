/-
Checked semantic bridges for generated PO classes.

These records are deliberately proof-carrying. A generated formula is not treated as
an Event-B semantic fact until the caller supplies the source binding, the semantic
precondition bridge, and the interpretation equivalence for the relevant contract.
-/

import EventB.POGSoundness
import EventB.Semantics

namespace EventB.POG

universe u

def eqlTerm (varName : String) : EventB.Formula.Term :=
  .bin "=" (.id (varName ++ "'")) (.id varName)

def transitionDenote (σ : Type u) :=
  EventB.Formula.Term → (σ × σ) → Prop

def transitionHypothesesHold {σ : Type u}
    (denote : transitionDenote σ) (hypotheses : List EventB.Formula.Term)
    (before after : σ) : Prop :=
  ∀ hypothesis ∈ hypotheses, denote hypothesis (before, after)

/- The source fields are intentionally redundant with `checked`: they make the
   machine/event/variable identity visible to consumers and prevent an adapter from
   silently changing the identity while reusing a proof. -/
structure EqlBridge (σ : Type u) (α : Type u) where
  theory : EventB.Theory.Env
  project : EventB.Typing.Project
  obligation : Obligation
  event : String
  varName : String
  read : σ → α
  action : σ → σ → Prop
  denote : transitionDenote σ
  checked : obligation.checkedIn theory project
  sourceName : obligation.name = event ++ "/" ++ varName ++ "/EQL"
  sourceKind : obligation.kind = "EQL"
  sourceGoal : obligation.goal = some (eqlTerm varName)
  hypothesesImplyAction : ∀ before after,
    transitionHypothesesHold denote obligation.hyps before after → action before after
  goalDenotesFrame : ∀ before after,
    denote (eqlTerm varName) (before, after) ↔ read after = read before
  frame : framePreserved read action

def EqlBridge.valid {σ α : Type u} (bridge : EqlBridge σ α) : Prop :=
  validSequent
    (bridge.obligation.hyps.map (fun hypothesis state => bridge.denote hypothesis state))
    (fun state => bridge.denote (eqlTerm bridge.varName) state)

theorem EqlBridge.valid_of_frame {σ α : Type u} (bridge : EqlBridge σ α) : bridge.valid := by
  intro state hypotheses
  rcases state with ⟨before, after⟩
  have hypothesesHold : transitionHypothesesHold bridge.denote bridge.obligation.hyps
      before after := by
    intro hypothesis member
    exact hypotheses (bridge.denote hypothesis)
      (List.mem_map.mpr ⟨hypothesis, member, rfl⟩)
  exact (bridge.goalDenotesFrame before after).mpr
    (bridge.frame before after (bridge.hypothesesImplyAction before after hypothesesHold))

/- A source-bound bridge cannot be built from a changed EQL goal. This is a small
   negative control independent of any evaluator implementation. -/
example {σ α : Type u} (bridge : EqlBridge σ α) :
    bridge.obligation.goal = some (eqlTerm bridge.varName) := bridge.sourceGoal

end EventB.POG
