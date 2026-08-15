/-
Event-B without Rodin: shallow embedding in Lean 4.
No Mathlib. `lean EventB.lean` type-checks everything, proofs included.

ponytail: no DSL parser, no AST, no PO generator binary. A machine is a Lean
value; the POs are the fields of `Proved` / `Refines`. Add surface syntax
(`syntax`/`macro_rules`) only when writing these records by hand hurts.
-/

universe u v

/-- Guarded event: guard on the pre-state, action as a before-after relation. -/
structure Event (σ : Type u) where
  grd : σ → Prop
  act : σ → σ → Prop

/-- Event-B events with explicit local parameters.  The parameter is chosen once
    before the guard and action are evaluated; it is never smuggled into the
    machine state or reused from another event. -/
structure ParameterizedEvent (σ : Type u) (π : Type v) where
  grd : π → σ → Prop
  act : π → σ → σ → Prop

def ParameterizedEvent.enabled {σ : Type u} {π : Type v}
    (event : ParameterizedEvent σ π) (state : σ) : Prop :=
  ∃ parameter, event.grd parameter state

def ParameterizedEvent.step {σ : Type u} {π : Type v}
    (event : ParameterizedEvent σ π) (before after : σ) : Prop :=
  ∃ parameter, event.grd parameter before ∧ event.act parameter before after

def ParameterizedEvent.invariantPreserved {σ : Type u} {π : Type v}
    (event : ParameterizedEvent σ π) (invariant : σ → Prop) : Prop :=
  ∀ parameter before after, invariant before → event.grd parameter before →
    event.act parameter before after → invariant after

theorem ParameterizedEvent.step_invariant {σ : Type u} {π : Type v}
    {event : ParameterizedEvent σ π} {invariant : σ → Prop}
    (preserved : event.invariantPreserved invariant) :
    ∀ before after, invariant before → event.step before after → invariant after := by
  intro before after invariantBefore step
  obtain ⟨parameter, guard, action⟩ := step
  exact preserved parameter before after invariantBefore guard action

/-- A local parameterized refinement contract.  The abstract parameter is selected
    from the concrete parameter and glued states, so enabledness and simulation use
    the same witness rather than an unrelated abstract event. -/
structure ParameterizedEventRefinement
    {γ α : Type u} {πγ πα : Type v}
    (concrete : ParameterizedEvent γ πγ) (abstract : ParameterizedEvent α πα)
    (gluing : γ → α → Prop) : Prop where
  guard : ∀ parameter concreteState abstractState,
    gluing concreteState abstractState → concrete.grd parameter concreteState →
      ∃ abstractParameter, abstract.grd abstractParameter abstractState
  action : ∀ parameter concreteState concreteAfter abstractState,
    gluing concreteState abstractState → concrete.grd parameter concreteState →
      concrete.act parameter concreteState concreteAfter →
      ∃ abstractParameter abstractAfter,
        abstract.grd abstractParameter abstractState ∧
          abstract.act abstractParameter abstractState abstractAfter ∧
          gluing concreteAfter abstractAfter

theorem ParameterizedEventRefinement.stepSim
    {γ α : Type u} {πγ πα : Type v}
    {concrete : ParameterizedEvent γ πγ} {abstract : ParameterizedEvent α πα}
    {gluing : γ → α → Prop}
    (contract : ParameterizedEventRefinement concrete abstract gluing) :
    ∀ concreteState concreteAfter abstractState,
      gluing concreteState abstractState →
      concrete.step concreteState concreteAfter →
        ∃ abstractAfter, abstract.step abstractState abstractAfter ∧
          gluing concreteAfter abstractAfter := by
  intro concreteState concreteAfter abstractState glued step
  obtain ⟨parameter, guard, action⟩ := step
  obtain ⟨abstractParameter, abstractAfter, abstractGuard, abstractAction, gluedAfter⟩ :=
    contract.action parameter concreteState concreteAfter abstractState glued guard action
  exact ⟨abstractAfter, ⟨abstractParameter, abstractGuard, abstractAction⟩, gluedAfter⟩

/-- A deterministic before-after relation. The state update is evaluated from the
pre-state, which is the semantic rule for parallel assignment. -/
def functionalAction {σ : Type u} (update : σ → σ) : σ → σ → Prop :=
  fun before after => after = update before

def deterministicAction {σ : Type u} (action : σ → σ → Prop) : Prop :=
  ∀ before after₁ after₂, action before after₁ → action before after₂ → after₁ = after₂

theorem functionalAction_deterministic {σ : Type u} (update : σ → σ) :
    deterministicAction (functionalAction update) := by
  intro before after₁ after₂ h₁ h₂
  simpa [functionalAction] using h₁.trans h₂.symm

def State (α : Type u) := String → α

def State.update {α : Type u} (state : State α) (name : String) (value : α) : State α :=
  fun current => if current == name then value else state current

/-- Parallel assignments read every right-hand side from the same pre-state. -/
def parallelUpdate {α : Type u} (updates : List (String × (State α → α)))
    (state : State α) : State α :=
  fun name => match updates.find? (·.1 == name) with
    | some (_, rhs) => rhs state
    | none => state name

theorem parallelUpdate_deterministic {α : Type u} (updates : List (String × (State α → α))) :
    deterministicAction
      (functionalAction (fun state : State α => parallelUpdate updates state)) := by
  intro before after₁ after₂ h₁ h₂
  simpa [functionalAction] using h₁.trans h₂.symm

theorem State.update_same {α : Type u} (state : State α) (name : String) (value : α) :
    State.update state name value name = value := by
  simp [State.update]

theorem State.update_other {α : Type u} (state : State α) {name other : String}
    (different : other ≠ name) (value : α) :
    State.update state name value other = state other := by
  simp [State.update, different]

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

/-- Event-local invariant proof obligations assembled into the machine proof. -/
structure InvariantProof {σ : Type u} (M : Machine σ) : Prop where
  init : ∀ s, M.init s → M.inv s
  event : ∀ e, e ∈ M.events → ∀ s s', M.inv s → e.grd s → e.act s s' → M.inv s'

theorem InvariantProof.toProved {σ : Type u} {M : Machine σ} (h : InvariantProof M) :
    Proved M := by
  constructor
  · exact h.init
  · rintro s s' hi ⟨e, he, hg, ha⟩
    exact h.event e he s s' hi hg ha

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

/-- Local refinement contract for one concrete event. It makes guard strengthening,
action simulation, and target-event membership explicit instead of hiding them in a
single opaque machine-level relation. -/
structure EventRefinement {γ α : Type u} (C : Machine γ) (A : Machine α)
    (J : γ → α → Prop) : Type (max u u) where
  abstractEvent : Event γ → Event α
  abstractMember : ∀ concrete, concrete ∈ C.events → abstractEvent concrete ∈ A.events
  guard : ∀ concrete c a, concrete ∈ C.events → J c a → concrete.grd c →
    (abstractEvent concrete).grd a
  action : ∀ concrete c c' a, concrete ∈ C.events → J c a → concrete.grd c →
    concrete.act c c' → ∃ a', (abstractEvent concrete).act a a' ∧ J c' a'

theorem EventRefinement.stepSim {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : EventRefinement C A J) :
    ∀ c c' a, J c a → C.step c c' → ∃ a', A.step a a' ∧ J c' a' := by
  rintro c c' a hJ ⟨concrete, concreteMember, concreteGuard, concreteAction⟩
  let abstract := h.abstractEvent concrete
  have abstractMember : abstract ∈ A.events := h.abstractMember concrete concreteMember
  have abstractGuard := h.guard concrete c a concreteMember hJ concreteGuard
  obtain ⟨a', abstractAction, hJ'⟩ :=
    h.action concrete c c' a concreteMember hJ concreteGuard concreteAction
  exact ⟨a', ⟨abstract, abstractMember, abstractGuard, abstractAction⟩, hJ'⟩

/-- A complete refinement proof separates initialization simulation from local event
contracts, then derives the machine-level simulation used by reachability theorems. -/
structure RefinementProof {γ α : Type u} (C : Machine γ) (A : Machine α)
    (J : γ → α → Prop) : Type (max u u) where
  init : ∀ c, C.init c → ∃ a, A.init a ∧ J c a
  events : EventRefinement C A J

theorem RefinementProof.toRefines {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : RefinementProof C A J) : Refines C A J := by
  exact { initSim := h.init, stepSim := h.events.stepSim }

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
/- Named contracts for refinement-heavy PO classes. These are semantic
   interfaces: a parser/POG supplies the formulas, while a model supplies
   their meaning and a proof supplies the contract. -/

def State.frame {α : Type u} (names : List String)
    (before after : State α) : Prop :=
  ∀ name, name ∈ names → after name = before name

def framePreserved {σ : Type u} {α : Type v} (read : σ → α)
    (action : σ → σ → Prop) : Prop :=
  ∀ before after, action before after → read after = read before

theorem State.parallelUpdate_frame_at {α : Type u}
    (updates : List (String × (State α → α))) (state : State α)
    {name : String}
    (notUpdated : ∀ update ∈ updates, update.1 ≠ name) :
    parallelUpdate updates state name = state name := by
  induction updates with
  | nil => rfl
  | cons head tail ih =>
      have headNotUpdated : head.1 ≠ name := notUpdated head (by simp)
      have tailNotUpdated : ∀ update ∈ tail, update.1 ≠ name := by
        intro update member
        exact notUpdated update (by simp [member])
      simp only [parallelUpdate, List.find?_cons]
      by_cases equal : head.1 == name
      · exact False.elim (headNotUpdated (eq_of_beq equal))
      · simp [equal]
        exact ih tailNotUpdated

theorem State.frame_of_parallelUpdate {α : Type u}
    (updates : List (String × (State α → α))) (state : State α)
    (names : List String)
    (notUpdated : ∀ name, name ∈ names → ∀ update ∈ updates, update.1 ≠ name) :
    State.frame names state (parallelUpdate updates state) := by
  intro name member
  exact State.parallelUpdate_frame_at updates state (notUpdated name member)

def gluingPreserved {γ α : Type u} (J : γ → α → Prop)
    (concrete : Event γ) (abstract : Event α) : Prop :=
  ∀ c c' a, J c a → concrete.grd c → concrete.act c c' →
    ∃ a', abstract.act a a' ∧ J c' a'

def guardStrengthened {γ α : Type u} (J : γ → α → Prop)
    (concrete : Event γ) (abstract : Event α) : Prop :=
  ∀ c a, J c a → concrete.grd c → abstract.grd a

def actionSimulates {γ α : Type u} (J : γ → α → Prop)
    (concrete : Event γ) (abstract : Event α) : Prop :=
  ∀ c c' a, J c a → concrete.grd c → concrete.act c c' →
    ∃ a', abstract.act a a' ∧ J c' a'

theorem EventRefinement.guardPO {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : EventRefinement C A J)
    (concrete : Event γ) (member : concrete ∈ C.events) :
    guardStrengthened J concrete (h.abstractEvent concrete) := by
  intro c a hJ guard
  exact h.guard concrete c a member hJ guard

theorem EventRefinement.actionPO {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : EventRefinement C A J)
    (concrete : Event γ) (member : concrete ∈ C.events) :
    actionSimulates J concrete (h.abstractEvent concrete) := by
  intro c c' a hJ guard action
  exact h.action concrete c c' a member hJ guard action

theorem EventRefinement.gluingPO {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : EventRefinement C A J)
    (concrete : Event γ) (member : concrete ∈ C.events) :
    gluingPreserved J concrete (h.abstractEvent concrete) :=
  h.actionPO concrete member

structure WitnessContract (σ α : Type u) (pre : σ → Prop)
    (defined : σ → Prop) (predicate : σ → α → Prop) : Prop where
  feasible : ∀ state, pre state → ∃ witness, predicate state witness
  wellDefined : ∀ state, pre state → defined state

def nonIncreasing {σ : Type u} (variant : σ → Nat)
    (action : σ → σ → Prop) : Prop :=
  ∀ before after, action before after → variant after ≤ variant before

def strictlyDecreases {σ : Type u} (variant : σ → Nat)
    (action : σ → σ → Prop) : Prop :=
  ∀ before after, action before after → variant after < variant before

structure AnticipatedVariant (σ : Type u) where
  measure : σ → Nat
  action : σ → σ → Prop
  nonIncrease : nonIncreasing measure action

structure ConvergentVariant (σ : Type u) where
  measure : σ → Nat
  action : σ → σ → Prop
  decrease : strictlyDecreases measure action

inductive IntegerVariantMode where
  | anticipated
  | convergent

def integerVariantProgress : IntegerVariantMode → Int → Int → Prop
  | .anticipated, after, before => after ≤ before
  | .convergent, after, before => after < before

/- Set-valued variants use extensional list membership.  The representation is finite by
   construction; the progress relation keeps anticipated subset and convergent proper
   subset distinct instead of collapsing both into a numeric measure. -/
inductive FiniteVariantMode where
  | anticipated
  | convergent

def finiteSubset {α : Type u} (after before : List α) : Prop :=
  ∀ value, value ∈ after → value ∈ before

def finiteProperSubset {α : Type u} (after before : List α) : Prop :=
  finiteSubset after before ∧ ∃ value, value ∈ before ∧ value ∉ after

def finiteVariantProgress {α : Type u} : FiniteVariantMode → List α → List α → Prop
  | .anticipated, after, before => finiteSubset after before
  | .convergent, after, before => finiteProperSubset after before

example : finiteVariantProgress .anticipated [1] [1, 2] := by
  intro value member
  simp_all

example : ¬ finiteVariantProgress .convergent [1] [1] := by
  intro progress
  rcases progress.2 with ⟨value, member, absent⟩
  simp_all

structure FiniteSetVariant (σ : Type u) (α : Type v) where
  mode : FiniteVariantMode
  measure : σ → List α
  action : σ → σ → Prop
  finite : σ → Prop
  progress : ∀ before after, action before after →
    finiteVariantProgress mode (measure after) (measure before)

/- An integer variant carries one semantic source identity shared by its naturality
   (NAT) and progress (VAR) obligations. The adapter that knows POG names maps both
   obligations to this identity; this layer does not depend on that representation. -/
structure IntegerVariant (σ : Type u) where
  source : String
  mode : IntegerVariantMode
  measure : σ → Int
  action : σ → σ → Prop
  natural : ∀ state, 0 ≤ measure state
  progress : ∀ before after, action before after →
    integerVariantProgress mode (measure after) (measure before)

def integerVariantNaturality {σ : Type u} (contract : IntegerVariant σ) : Prop :=
  ∀ state, 0 ≤ contract.measure state

def integerVariantProgressSemantic {σ : Type u} (contract : IntegerVariant σ) : Prop :=
  ∀ before after, contract.action before after →
    integerVariantProgress contract.mode
      (contract.measure after) (contract.measure before)

def finiteVariantFiniteness {σ : Type u} {α : Type v}
    (contract : FiniteSetVariant σ α) : Prop :=
  ∀ state, contract.finite state

def finiteVariantProgressSemantic {σ : Type u} {α : Type v}
    (contract : FiniteSetVariant σ α) : Prop :=
  ∀ before after, contract.action before after →
    finiteVariantProgress contract.mode
      (contract.measure after) (contract.measure before)

/-- A general VAR contract.  The measure need not be numeric or represented as a
    finite list; strict progress is checked against an explicitly supplied
    well-founded relation, while anticipated non-increase remains a separate
    contract above. -/
structure WellFoundedVariant (σ : Type u) (α : Type v) where
  measure : σ → α
  relation : α → α → Prop
  wellFounded : WellFounded relation
  action : σ → σ → Prop
  progress : ∀ before after, action before after →
    relation (measure after) (measure before)

def wellFoundedVariantProgressSemantic {σ : Type u} {α : Type v}
    (contract : WellFoundedVariant σ α) : Prop :=
  ∀ before after, contract.action before after →
    contract.relation (contract.measure after) (contract.measure before)

theorem WellFoundedVariant.progressSemantic {σ : Type u} {α : Type v}
    (contract : WellFoundedVariant σ α) :
    wellFoundedVariantProgressSemantic contract :=
  contract.progress

/- A merge contract names the event coverage that is otherwise easy to lose when
   several concrete events refine one abstract event. -/
structure MergeSimulation {γ α : Type u} (C : Machine γ) (A : Machine α)
    (J : γ → α → Prop) : Type (max u u) where
  abstractEvent : Event α
  abstractMember : abstractEvent ∈ A.events
  concreteEvents : List (Event γ)
  covered : ∀ concrete, concrete ∈ C.events → concrete ∈ concreteEvents
  member : ∀ concrete, concrete ∈ concreteEvents → concrete ∈ C.events
  guard : ∀ concrete c a, concrete ∈ concreteEvents → J c a → concrete.grd c →
    abstractEvent.grd a
  action : ∀ concrete c c' a, concrete ∈ concreteEvents → J c a → concrete.grd c →
    concrete.act c c' → ∃ a', abstractEvent.act a a' ∧ J c' a'

theorem MergeSimulation.stepSim {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : MergeSimulation C A J) :
    ∀ c c' a, J c a → C.step c c' → ∃ a', A.step a a' ∧ J c' a' := by
  rintro c c' a hJ ⟨concrete, concreteMember, concreteGuard, concreteAction⟩
  have concreteInMerge := h.covered concrete concreteMember
  have abstractGuard := h.guard concrete c a concreteInMerge hJ concreteGuard
  obtain ⟨a', abstractAction, hJ'⟩ :=
    h.action concrete c c' a concreteInMerge hJ concreteGuard concreteAction
  exact ⟨a', ⟨h.abstractEvent, h.abstractMember, abstractGuard, abstractAction⟩, hJ'⟩

/- A split contract handles one concrete event whose enabled behavior may select one
   of several abstract events. The step theorem is local to the named concrete event;
   other concrete events require their own refinement contract. -/
structure SplitSimulation {γ α : Type u} (C : Machine γ) (A : Machine α)
    (J : γ → α → Prop) : Type (max u u) where
  concreteEvent : Event γ
  concreteMember : concreteEvent ∈ C.events
  abstractEvents : List (Event α)
  abstractNonempty : abstractEvents ≠ []
  abstractMember : ∀ abstract, abstract ∈ abstractEvents → abstract ∈ A.events
  guard : ∀ c a, J c a → concreteEvent.grd c →
    ∃ abstract, abstract ∈ abstractEvents ∧ abstract.grd a
  action : ∀ abstract c c' a, abstract ∈ abstractEvents → J c a →
    concreteEvent.grd c → abstract.grd a → concreteEvent.act c c' →
    ∃ a', abstract.act a a' ∧ J c' a'

theorem SplitSimulation.stepSim {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (h : SplitSimulation C A J) :
    ∀ c c' a, J c a → h.concreteEvent.grd c → h.concreteEvent.act c c' →
      ∃ a', A.step a a' ∧ J c' a' := by
  intro c c' a hJ concreteGuard concreteAction
  obtain ⟨abstract, abstractMember, abstractGuard⟩ := h.guard c a hJ concreteGuard
  obtain ⟨a', abstractAction, hJ'⟩ :=
    h.action abstract c c' a abstractMember hJ concreteGuard abstractGuard concreteAction
  exact ⟨a', ⟨abstract, h.abstractMember abstract abstractMember,
    abstractGuard, abstractAction⟩, hJ'⟩

def variantDecreasesAt (variant : Nat → Nat) (before after : Nat) : Bool :=
  variant after < variant before

#guard !variantDecreasesAt (fun _ => 0) 0 0

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

def C_event_refinement : EventRefinement C A J := by
  refine { abstractEvent := fun _ => incA, abstractMember := ?_, guard := ?_, action := ?_ }
  · intro concrete hconcrete
    have : concrete = incC := mem_single hconcrete
    subst this
    exact List.mem_singleton.mpr rfl
  · intro concrete c n hconcrete hJ hg
    have : concrete = incC := mem_single hconcrete
    subst this
    have h2 : 0 < c.2 := hg
    have hJ1 : c.1 = n := hJ.1
    have hJ2 : c.1 + c.2 = 10 := hJ.2
    show n < 10
    omega
  · intro concrete c c' n hconcrete hJ hg ha
    have : concrete = incC := mem_single hconcrete
    subst this
    have h2 : 0 < c.2 := hg
    have hJ1 : c.1 = n := hJ.1
    have hJ2 : c.1 + c.2 = 10 := hJ.2
    have h3 : c' = (c.1 + 1, c.2 - 1) := ha
    subst h3
    have abstractAction : incA.act n (n + 1) := rfl
    exact ⟨n + 1, abstractAction, by
      show c.1 + 1 = n + 1 ∧ (c.1 + 1) + (c.2 - 1) = 10
      omega⟩

def C_merge_refinement : MergeSimulation C A J := by
  refine
    { abstractEvent := incA
      abstractMember := ?_
      concreteEvents := [incC]
      covered := ?_
      member := ?_
      guard := ?_
      action := ?_ }
  · exact List.mem_singleton.mpr rfl
  · intro concrete hconcrete
    have : concrete = incC := mem_single hconcrete
    subst this
    exact List.mem_singleton.mpr rfl
  · intro concrete hconcrete
    have : concrete = incC := mem_single hconcrete
    subst this
    exact List.mem_singleton.mpr rfl
  · intro concrete c n hconcrete hJ hg
    have : concrete = incC := mem_single hconcrete
    subst this
    exact C_event_refinement.guard incC c n (List.mem_singleton.mpr rfl) hJ hg
  · intro concrete c c' n hconcrete hJ hg ha
    have : concrete = incC := mem_single hconcrete
    subst this
    exact C_event_refinement.action incC c c' n (List.mem_singleton.mpr rfl) hJ hg ha

theorem C_refines_A_from_merge_contract : Refines C A J := by
  refine { initSim := C_refines_A.initSim, stepSim := C_merge_refinement.stepSim }

theorem positiveWitness : WitnessContract Unit Unit
    (fun _ => True) (fun _ => True) (fun _ _ => True) :=
  { feasible := fun _ _ => ⟨(), trivial⟩
    wellDefined := fun _ _ => trivial }

def positiveConvergentVariant : ConvergentVariant (Nat × Nat) :=
  { measure := fun state => state.2
    action := fun before after => incC.grd before ∧ incC.act before after
    decrease := by
      intro before after action
      have afterState : after = (before.1 + 1, before.2 - 1) := action.2
      have enabled : 0 < before.2 := action.1
      rw [afterState]
      change before.2 - 1 < before.2
      omega }

def C_local_refinement : RefinementProof C A J :=
  { init := C_refines_A.initSim, events := C_event_refinement }

theorem C_refines_A_from_event_contracts : Refines C A J :=
  C_local_refinement.toRefines

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
