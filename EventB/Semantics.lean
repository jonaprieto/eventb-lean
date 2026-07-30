/-
Event-B without Rodin: shallow embedding in Lean 4.
No Mathlib. `lean EventB.lean` type-checks everything, proofs included.

ponytail: no DSL parser, no AST, no PO generator binary. A machine is a Lean
value; the POs are the fields of `Proved` / `Refines`. Add surface syntax
(`syntax`/`macro_rules`) only when writing these records by hand hurts.
-/

universe u

/-- Guarded event: guard on the pre-state, action as a before-after relation. -/
structure Event (σ : Type u) where
  grd : σ → Prop
  act : σ → σ → Prop

/-- Event-B machine. `inv` is the invariant, `init` the initialisation predicate. -/
structure Machine (σ : Type u) where
  inv    : σ → Prop
  init   : σ → Prop
  events : List (Event σ)

/-- One step = some enabled event fires. -/
def Machine.step {σ : Type u} (M : Machine σ) (s s' : σ) : Prop :=
  ∃ e ∈ M.events, e.grd s ∧ e.act s s'

/-- Reachable states. -/
inductive Reach {σ : Type u} (M : Machine σ) : σ → Prop where
  | init {s}    : M.init s → Reach M s
  | step {s s'} : Reach M s → M.step s s' → Reach M s'

/-- The two consistency POs Rodin's POG would emit: INV/INITIALISATION and INV/event. -/
structure Proved {σ : Type u} (M : Machine σ) : Prop where
  invInit : ∀ s, M.init s → M.inv s
  invStep : ∀ s s', M.inv s → M.step s s' → M.inv s'

/-- Discharged POs ⟹ invariant holds on every reachable state. -/
theorem Proved.sound {σ : Type u} {M : Machine σ} (h : Proved M) :
    ∀ s, Reach M s → M.inv s := by
  intro s r
  induction r with
  | init hi      => exact h.invInit _ hi
  | step _ hs ih => exact h.invStep _ _ ih hs

/-- Refinement POs, gluing invariant `J`. Forward simulation. -/
structure Refines {γ α : Type u} (C : Machine γ) (A : Machine α) (J : γ → α → Prop) : Prop where
  initSim : ∀ c, C.init c → ∃ a, A.init a ∧ J c a
  stepSim : ∀ c c' a, J c a → C.step c c' → ∃ a', A.step a a' ∧ J c' a'

/-- Soundness: every reachable concrete state is glued to a reachable abstract state. -/
theorem Refines.sound {γ α : Type u} {C : Machine γ} {A : Machine α} {J : γ → α → Prop}
    (h : Refines C A J) : ∀ c, Reach C c → ∃ a, Reach A a ∧ J c a := by
  intro c r
  induction r with
  | init hi =>
      obtain ⟨a, ha, hJ⟩ := h.initSim _ hi
      exact ⟨a, .init ha, hJ⟩
  | step _ hs ih =>
      obtain ⟨a, hra, hJ⟩ := ih
      obtain ⟨a', ha', hJ'⟩ := h.stepSim _ _ _ hJ hs
      exact ⟨a', .step hra ha', hJ'⟩

/-- Abstract invariant transfers to the refinement for free. -/
theorem Refines.inv_transfer {γ α : Type u} {C : Machine γ} {A : Machine α} {J : γ → α → Prop}
    (hr : Refines C A J) (hp : Proved A) :
    ∀ c, Reach C c → ∃ a, A.inv a ∧ J c a := by
  intro c r
  obtain ⟨a, hra, hJ⟩ := hr.sound c r
  exact ⟨a, hp.sound a hra, hJ⟩

/- ------------------------------------------------------------------ -/
/- Self-check: bounded counter, refined by (counter, remaining budget). -/

theorem mem_single {α : Type u} {a b : α} (h : a ∈ [b]) : a = b := by
  simp at h; exact h

/-- Abstract: `n` counts up to 10. -/
def incA : Event Nat := { grd := fun n => n < 10, act := fun n n' => n' = n + 1 }
def A : Machine Nat :=
  { inv := fun n => n ≤ 10, init := fun n => n = 0, events := [incA] }

/-- Concrete: carries the variant `10 - n` explicitly; the guard reads the budget. -/
def incC : Event (Nat × Nat) :=
  { grd := fun c => 0 < c.2, act := fun c c' => c' = (c.1 + 1, c.2 - 1) }
def C : Machine (Nat × Nat) :=
  { inv := fun c => c.1 + c.2 = 10, init := fun c => c = (0, 10), events := [incC] }

/-- Gluing invariant. -/
def J : Nat × Nat → Nat → Prop := fun c n => c.1 = n ∧ c.1 + c.2 = 10

theorem A_proved : Proved A := by
  constructor
  · intro s hs
    have : s = 0 := hs
    show s ≤ 10
    omega
  · rintro s s' hi ⟨e, he, hg, ha⟩
    have he' := mem_single he; subst he'
    have h1 : s ≤ 10 := hi
    have h2 : s < 10 := hg
    have h3 : s' = s + 1 := ha
    show s' ≤ 10
    omega

theorem C_refines_A : Refines C A J := by
  constructor
  · intro c hc
    have : c = (0, 10) := hc
    subst this
    exact ⟨0, rfl, rfl, rfl⟩
  · rintro c c' n ⟨hJ1, hJ2⟩ ⟨e, he, hg, ha⟩
    have he' := mem_single he; subst he'
    have h2 : 0 < c.2 := hg
    have h3 : c' = (c.1 + 1, c.2 - 1) := ha
    subst h3
    exact ⟨n + 1, ⟨incA, List.mem_singleton.mpr rfl, by show n < 10; omega, rfl⟩,
           by show c.1 + 1 = n + 1 ∧ (c.1 + 1) + (c.2 - 1) = 10; omega⟩

/-- The payoff: concrete machine inherits `n ≤ 10` without re-proving it. -/
example : ∀ c, Reach C c → c.1 ≤ 10 := by
  intro c r
  obtain ⟨n, hn, hJ⟩ := C_refines_A.inv_transfer A_proved c r
  have h1 : n ≤ 10 := hn
  have h2 : c.1 = n := hJ.1
  omega

#print axioms Proved.sound
#print axioms Refines.sound
#print axioms C_refines_A
