/-
Event-B set theory in Lean, over Mathlib's `Set`.

This is what a proof-obligation generator would have to emit into, so the spike measures
Lean's discharge rate against these definitions rather than against hand-massaged goals.
Every operator here is spelled the way Event-B means it: a relation is a set of pairs, a
function is a relation that happens to be functional, and application is only defined
where the argument is in the domain.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.SetNotation

namespace B

universe u v w

/-- Event-B relations are sets of pairs; nothing distinguishes a relation from a
function at the type level, which is exactly why so many obligations are about
functionality. -/
abbrev Rel (α : Type u) (β : Type v) := Set (α × β)

variable {α : Type u} {β : Type v} {γ : Type w}

def dom (r : Rel α β) : Set α := {a | ∃ b, (a, b) ∈ r}
def ran (r : Rel α β) : Set β := {b | ∃ a, (a, b) ∈ r}

/-- Relational image `r[s]`. -/
def image (r : Rel α β) (s : Set α) : Set β := {b | ∃ a ∈ s, (a, b) ∈ r}

/-- Inverse `r∼`. -/
def inv (r : Rel α β) : Rel β α := {p | (p.2, p.1) ∈ r}

def domRes (s : Set α) (r : Rel α β) : Rel α β := {p ∈ r | p.1 ∈ s}
def domSub (s : Set α) (r : Rel α β) : Rel α β := {p ∈ r | p.1 ∉ s}
def ranRes (r : Rel α β) (s : Set β) : Rel α β := {p ∈ r | p.2 ∈ s}
def ranSub (r : Rel α β) (s : Set β) : Rel α β := {p ∈ r | p.2 ∉ s}

/-- Override `r  q`: `q` wins wherever it is defined. -/
def override (r q : Rel α β) : Rel α β := q ∪ domSub (dom q) r

def comp (r : Rel α β) (q : Rel β γ) : Rel α γ := {p | ∃ b, (p.1, b) ∈ r ∧ (b, p.2) ∈ q}

/-- `r` is functional: no argument is related to two results. -/
def IsFun (r : Rel α β) : Prop := ∀ a b₁ b₂, (a, b₁) ∈ r → (a, b₂) ∈ r → b₁ = b₂

/-- The arrow families, each a *set of relations*, which is how Event-B states them and
why membership in an arrow is a predicate rather than a typing judgement. -/
def rel (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | dom r ⊆ s ∧ ran r ⊆ t}
def pfun (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ rel s t ∧ IsFun r}
def tfun (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ pfun s t ∧ dom r = s}
def pinj (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ pfun s t ∧ IsFun (inv r)}
def tinj (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ tfun s t ∧ IsFun (inv r)}
def psurj (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ pfun s t ∧ ran r = t}
def tsurj (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ tfun s t ∧ ran r = t}
def tbij (s : Set α) (t : Set β) : Set (Rel α β) :=
  {r | r ∈ tinj s t ∧ ran r = t}

/-- Cartesian product as an Event-B *value*, a set of pairs. -/
def prod (s : Set α) (t : Set β) : Rel α β := {p | p.1 ∈ s ∧ p.2 ∈ t}

/-- Integer range `a ‥ b`. -/
def upto (a b : Int) : Set Int := {n | a ≤ n ∧ n ≤ b}

/-- `ℕ` as a subset of `ℤ`, which is how Event-B uses it. -/
def NAT : Set Int := {n | 0 ≤ n}
def NAT1 : Set Int := {n | 1 ≤ n}

/-- Function application. Event-B's `f(x)` is defined only when `x ∈ dom f` and `f` is
functional there; outside that it is an arbitrary value, and the well-definedness
obligation is what rules the bad case out. Choice is the honest encoding: it makes `f(x)`
total in Lean while leaving every fact about it dependent on the WD hypothesis. -/
noncomputable def app [Nonempty β] (f : Rel α β) (a : α) : β :=
  open Classical in
  if h : ∃ b, (a, b) ∈ f then h.choose else Classical.arbitrary β

theorem app_mem [Nonempty β] {f : Rel α β} {a : α} (h : ∃ b, (a, b) ∈ f) :
    (a, app f a) ∈ f := by
  simp only [app, dif_pos h]
  exact h.choose_spec

theorem app_eq [Nonempty β] {f : Rel α β} {a : α} {b : β}
    (hf : IsFun f) (hab : (a, b) ∈ f) : app f a = b :=
  hf a _ _ (app_mem ⟨b, hab⟩) hab

end B
