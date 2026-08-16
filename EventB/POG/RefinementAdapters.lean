/-
Proof-carrying adapters for the refinement-heavy PO families.  They bind the exact
checked generated record to the corresponding semantic contract, but deliberately
do not infer a semantic proof from a PO name or from an arbitrary formula model.
-/

import EventB.POGSoundness
import EventB.Semantics

namespace EventB.POG

universe u v

structure CheckedPO (theory : EventB.Theory.Env) (project : EventB.Typing.Project) where
  obligation : Obligation
  checked : obligation.checkedIn theory project

private structure MemberResult (obligations : List Obligation) where
  obligation : Obligation
  member : obligation ∈ obligations

private def findMember (predicate : Obligation → Bool) (obligations : List Obligation) :
    Option (MemberResult obligations) :=
  match obligations with
  | [] => none
  | obligation :: rest =>
      if predicate obligation then
        some { obligation, member := by simp }
      else
        match findMember predicate rest with
        | none => none
        | some result => some { obligation := result.obligation, member := by simp [result.member] }

def CheckedPO.fromGenerated? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component : String)
    (predicate : Obligation → Bool) : Option (CheckedPO theory project) :=
  match generated : generateCheckedIn theory project component with
  | .error _ => none
  | .ok obligations =>
      match findMember predicate obligations with
      | none => none
      | some result =>
          let obligation := result.obligation
          if componentEq : obligation.component = component then
            if source : obligation.sourceBound project = true then
              some
                { obligation := obligation
                  checked := by
                    simp [Obligation.checkedIn, componentEq, generated, source]
                    simpa [componentEq, generated] using result.member }
          else none
          else none

private structure ExactMember (target : Obligation) (obligations : List Obligation) where
  payload : Unit
  member : target ∈ obligations

private def exactMember (target : Obligation) : (obligations : List Obligation) →
    Option (ExactMember target obligations)
  | [] => none
  | candidate :: rest =>
      if same : candidate = target then
        have member : target ∈ candidate :: rest := by
          subst target
          simp
        some { payload := (), member }
      else
        match exactMember target rest with
        | none => none
        | some result => some { payload := (), member := by simp [result.member] }

def CheckedPO.fromGeneratedExact? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (obligation : Obligation) :
    Option (CheckedPO theory project) :=
  match generated : generateCheckedIn theory project obligation.component with
  | .error _ => none
  | .ok obligations =>
      match exactMember obligation obligations with
      | none => none
      | some member =>
          if source : obligation.sourceBound project = true then
            some
              { obligation := obligation
                checked := by
                  simp [Obligation.checkedIn, generated, source]
                  exact member.member }
          else none

def exactComponentDeclarations? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component : String) :
    Option (List (String × EventB.Typing.Ty)) :=
  match EventB.Typing.inferComponentDetailsCheckedIn theory project component with
  | .ok details => some details.types
  | .error _ => none

def exactEventDeclarations? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) :
    Option (List (String × EventB.Typing.Ty)) :=
  match ComponentValuation.fromProject theory project component with
  | .ok valuation => some (valuation.declarationsForEvent project event)
  | .error _ => none

def exactScopedDeclarations? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component : String)
    (event : Option String) : Option (List (String × EventB.Typing.Ty)) :=
  match event with
  | none => exactComponentDeclarations? theory project component
  | some label => exactEventDeclarations? theory project component label

structure CheckedEventSource (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) where
  valuation : ComponentValuation
  valuationChecked :
    ComponentValuation.fromProject theory project component = .ok valuation
  declarations : List (String × EventB.Typing.Ty)
  declarationsExact :
    declarations = valuation.declarationsForEvent project event
  updates : List (String × EventB.Formula.Term)
  updatesExact : valuation.eventAssignments project event = .ok updates

def CheckedEventSource.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) :
    Option (CheckedEventSource theory project component event) :=
  match valuationChecked : ComponentValuation.fromProject theory project component with
  | .error _ => none
  | .ok valuation =>
      match updatesExact : valuation.eventAssignments project event with
      | .error _ => none
      | .ok updates =>
          some
            { valuation := valuation
              valuationChecked := valuationChecked
              declarations := valuation.declarationsForEvent project event
              declarationsExact := rfl
              updates := updates
              updatesExact := updatesExact }

def CheckedEventSource.assignmentAction
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {component event : String} (source : CheckedEventSource theory project component event)
    (fuel : Nat) (transition : CheckedBeforeAfter) : Prop :=
  assignmentRelation fuel source.declarations transition source.updates

structure CheckedGuardSource (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) where
  valuation : ComponentValuation
  valuationChecked :
    ComponentValuation.fromProject theory project component = .ok valuation
  declarations : List (String × EventB.Typing.Ty)
  declarationsExact :
    declarations = valuation.declarationsForEvent project event
  predicates : List EventB.Formula.Term
  predicatesExact : EventB.POG.eventGuardPredicates project component event = some predicates

def CheckedGuardSource.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) :
    Option (CheckedGuardSource theory project component event) :=
  match valuationChecked : ComponentValuation.fromProject theory project component with
  | .error _ => none
  | .ok valuation =>
      match predicatesExact : EventB.POG.eventGuardPredicates project component event with
      | none => none
      | some predicates =>
          some
            { valuation
              valuationChecked
              declarations := valuation.declarationsForEvent project event
              declarationsExact := rfl
              predicates
              predicatesExact }

def CheckedGuardSource.holds
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {component event : String} (source : CheckedGuardSource theory project component event)
    (fuel : Nat) (transition : CheckedBeforeAfter) : Prop :=
  transition.declarations = source.declarations ∧
    ValueEnv.validationOk fuel source.declarations transition.before = true ∧
    ValueEnv.validationOk fuel source.declarations transition.after = true ∧
    ∀ predicate ∈ source.predicates,
      assignmentPredicateWithFuel fuel transition predicate

/- Relational actions are a separate source type so deterministic assignment proofs
   cannot accidentally be weakened when a project uses :∈ or :∣. -/
structure CheckedRelationalEventSource (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) where
  valuation : ComponentValuation
  valuationChecked :
    ComponentValuation.fromProject theory project component = .ok valuation
  declarations : List (String × EventB.Typing.Ty)
  declarationsExact :
    declarations = valuation.declarationsForEvent project event
  relations : List EventB.Formula.Term
  relationsExact :
    relations = EventB.POG.eventStateRelations project component event valuation.variables
  relationsNonempty : relations ≠ []

def CheckedRelationalEventSource.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) :
    Option (CheckedRelationalEventSource theory project component event) :=
  match valuationChecked : ComponentValuation.fromProject theory project component with
  | .error _ => none
  | .ok valuation =>
      let relations := EventB.POG.eventStateRelations project component event valuation.variables
      if h : relations.isEmpty then none
      else
        some
          { valuation := valuation
            valuationChecked := valuationChecked
            declarations := valuation.declarationsForEvent project event
            declarationsExact := rfl
            relations
            relationsExact := rfl
            relationsNonempty := by simpa using h }

def CheckedRelationalEventSource.relationAction
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {component event : String}
    (source : CheckedRelationalEventSource theory project component event)
    (fuel : Nat) (transition : CheckedBeforeAfter) : Prop :=
  transition.declarations = source.declarations ∧
    ValueEnv.validationOk fuel source.declarations transition.before = true ∧
    ValueEnv.validationOk fuel source.declarations transition.after = true ∧
    ∀ relation ∈ source.relations,
      assignmentPredicateWithFuel fuel transition relation

def relationalEventActionExact {τ : Type u}
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {component event : String}
    (source : CheckedRelationalEventSource theory project component event)
    (fuel : Nat) (encode : τ → CheckedBeforeAfter) (action : τ → Prop) : Prop :=
  ∀ state, action state ↔ source.relationAction fuel (encode state)

/- MRG is source-sensitive in a different way from ordinary actions: one concrete
   event must name multiple abstract events.  Keep that target list tied to the
   parsed event so a caller cannot turn a single-event proof into a merge proof. -/
structure CheckedMergeSource (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) where
  eventSource : CheckedEventSource theory project component event
  targets : List String
  targetsExact : targets = EventB.POG.eventRefinementTargets project component event
  targetLocators : List (String × String)
  targetLocatorsExact :
    targetLocators = EventB.POG.eventRefinementTargetLocators project component event
  targetCount : targets.length > 1

def CheckedMergeSource.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event : String) :
    Option (CheckedMergeSource theory project component event) :=
  match CheckedEventSource.fromProject theory project component event with
  | none => none
  | some eventSource =>
      let targets := EventB.POG.eventRefinementTargets project component event
      let targetLocators := EventB.POG.eventRefinementTargetLocators project component event
      if h : targets.length > 1 then
        some
          { eventSource := eventSource
            targets := targets
            targetsExact := rfl
            targetLocators := targetLocators
            targetLocatorsExact := rfl
            targetCount := h }
      else none

def exactWitnessSource? (project : EventB.Typing.Project)
    (component event witness : String) : Option (String × EventB.Formula.Term) :=
  match EventB.Typing.lookupComponent project component with
  | none => none
  | some current =>
      match current.elem.children.find? (fun candidate =>
          candidate.tag == "org.eventb.core.event" &&
            candidate.attr? "org.eventb.core.label" == some event) with
      | none => none
      | some currentEvent =>
          match currentEvent.children.find? (fun candidate =>
              candidate.tag == "org.eventb.core.witness" &&
                candidate.attr? "org.eventb.core.label" == some witness) with
          | none => none
          | some currentWitness => do
              let witnessVariable ← EventB.POG.exactWitnessVariable? currentWitness
              let predicate ← EventB.POG.exactWitnessPredicate? currentWitness
              pure (witnessVariable, predicate)

/- Witness source identity is separate from the concrete event assignment source:
   an abstract parameter witness is not a deterministic concrete update. -/
structure CheckedWitnessSource (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event witness : String) where
  valuation : ComponentValuation
  valuationChecked :
    ComponentValuation.fromProject theory project component = .ok valuation
  declarations : List (String × EventB.Typing.Ty)
  declarationsExact :
    declarations = valuation.declarationsForEvent project event
  witnessVariable : String
  predicate : EventB.Formula.Term
  sourceExact : exactWitnessSource? project component event witness = some
    (witnessVariable, predicate)

def CheckedWitnessSource.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event witness : String) :
    Option (CheckedWitnessSource theory project component event witness) :=
  match valuationChecked : ComponentValuation.fromProject theory project component with
  | .error _ => none
  | .ok valuation =>
      match sourceExact : exactWitnessSource? project component event witness with
      | none => none
      | some (witnessVariable, predicate) =>
          some
            { valuation := valuation
              valuationChecked := valuationChecked
              declarations := valuation.declarationsForEvent project event
              declarationsExact := rfl
              witnessVariable
              predicate
              sourceExact }

theorem witnessSourceExact {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {component event witness : String}
    (source : CheckedWitnessSource theory project component event witness) :
    exactWitnessSource? project component event witness = some
      (source.witnessVariable, source.predicate) :=
  source.sourceExact

def exactVariantExpression? (project : EventB.Typing.Project) (component : String) :
    Option EventB.Formula.Term :=
  match EventB.Typing.lookupComponent project component with
  | none => none
  | some current =>
      match current.elem.children.filter (fun child =>
          child.tag == "org.eventb.core.variant") with
      | [variant] =>
          match variant.attr? "org.eventb.core.expression" with
          | none => none
          | some source => (EventB.Formula.parse source).toOption
      | _ => none

structure CheckedVariantSource (project : EventB.Typing.Project) (component : String) where
  expression : EventB.Formula.Term
  expressionExact : exactVariantExpression? project component = some expression

def CheckedVariantSource.fromProject (project : EventB.Typing.Project) (component : String) :
    Option (CheckedVariantSource project component) :=
  match expressionExact : exactVariantExpression? project component with
  | some expression => some { expression, expressionExact }
  | none => none

def eventActionExact {τ : Type u}
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {component event : String} (source : CheckedEventSource theory project component event)
    (fuel : Nat) (encode : τ → CheckedBeforeAfter) (action : τ → Prop) : Prop :=
  ∀ state, action state ↔ source.assignmentAction fuel (encode state)

/- One merge branch is accepted only when its abstract semantic event is connected to
   the exact parsed source event.  The semantic event remains a Lean value, but its
   guard and action must use the checked abstract source through the supplied encoder. -/
structure CheckedMergeBranch (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (α : Type u) where
  locator : String × String
  eventSource : CheckedEventSource theory project locator.1 locator.2
  guardSource : CheckedGuardSource theory project locator.1 locator.2
  event : Event α
  fuel : Nat
  encode : (α × α) → CheckedBeforeAfter
  actionExact : eventActionExact eventSource fuel encode
    (fun state => event.act state.1 state.2)
  guardExact : ∀ state, event.grd state.1 ↔ guardSource.holds fuel (encode state)

/- A formula is not a semantic contract merely because it has the right PO name.
   Every accepting adapter therefore uses the fixed typed evaluator, binds its
   declarations to strict component inference, validates the exact generated formula,
   and carries only the project-specific implication from that evaluator meaning to
   the semantic contract. -/
structure FormulaAdequacy {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : CheckedPO theory project)
    (τ : Type u) (semantic : Prop) where
  evaluator : TypedFormulaModel
  encode : τ → ValueEnv
  declarationScope : Option String
  declarationsBound :
    exactScopedDeclarations? theory project binding.obligation.component declarationScope =
      some evaluator.declarations
  stateValid : ∀ state, evaluator.wellFormed (encode state)
  stateComplete : ∀ env, evaluator.wellFormed env → ∃ state, encode state = env
  evaluatorValid : evaluator.validUnchecked binding.obligation
  adequate : FormulaModel.validUnchecked
      (evaluator.on encode) binding.obligation → semantic

theorem FormulaAdequacy.valid {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {binding : CheckedPO theory project}
    {τ : Type u} {semantic : Prop} (formula : FormulaAdequacy binding τ semantic) :
    FormulaModel.validUnchecked (formula.evaluator.on formula.encode) binding.obligation :=
  formula.evaluator.valid_on formula.encode binding.obligation
    formula.evaluatorValid formula.stateValid

theorem FormulaAdequacy.validWithCoverage {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {binding : CheckedPO theory project}
    {τ : Type u} {semantic : Prop} (formula : FormulaAdequacy binding τ semantic) :
    FormulaModel.validUnchecked (formula.evaluator.on formula.encode) binding.obligation ∧
      (∀ env, formula.evaluator.wellFormed env → ∃ state, formula.encode state = env) :=
  ⟨formula.valid, formula.stateComplete⟩

/- Adequacy for an invariant/reachability-restricted semantic state domain. The
   domain is explicit and coverage is required only over that domain; this is the
   missing counterpart to transition source coverage for non-total VAR actions. -/
structure DomainFormulaAdequacy {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : CheckedPO theory project)
    (τ : Type u) (semantic : Prop) (domain : ValueEnv → Prop) where
  evaluator : TypedFormulaModel
  encode : τ → ValueEnv
  declarationScope : Option String
  declarationsBound :
    exactScopedDeclarations? theory project binding.obligation.component declarationScope =
      some evaluator.declarations
  stateValid : ∀ state, domain (encode state)
  stateComplete : ∀ env, domain env → ∃ state, encode state = env
  evaluatorValid : evaluator.validOnDomain domain binding.obligation
  adequate : FormulaModel.validUnchecked
      (evaluator.on encode) binding.obligation → semantic

theorem DomainFormulaAdequacy.valid {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {binding : CheckedPO theory project}
    {τ : Type u} {semantic : Prop} {domain : ValueEnv → Prop}
    (formula : DomainFormulaAdequacy binding τ semantic domain) :
    FormulaModel.validUnchecked (formula.evaluator.on formula.encode) binding.obligation :=
  formula.evaluator.validOnDomain_on domain formula.encode binding.obligation
    formula.evaluatorValid formula.stateValid

theorem DomainFormulaAdequacy.validWithCoverage {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {binding : CheckedPO theory project}
    {τ : Type u} {semantic : Prop} {domain : ValueEnv → Prop}
    (formula : DomainFormulaAdequacy binding τ semantic domain) :
    FormulaModel.validUnchecked (formula.evaluator.on formula.encode) binding.obligation ∧
      (∀ env, domain env → ∃ state, formula.encode state = env) :=
  ⟨formula.valid, formula.stateComplete⟩

structure TransitionFormulaAdequacy {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : CheckedPO theory project)
    (τ : Type u) (semantic : Prop) (source : CheckedBeforeAfter → Prop) where
  evaluator : TypedTransitionModel
  encode : τ → CheckedBeforeAfter
  declarations : List (String × EventB.Typing.Ty)
  declarationScope : Option String
  declarationsBound :
    exactScopedDeclarations? theory project binding.obligation.component declarationScope =
      some declarations
  transitionDeclarations : ∀ state, (encode state).declarations = declarations
  transitionValid : ∀ state, evaluator.wellFormed (encode state)
  sourceValid : ∀ state, source (encode state)
  sourceComplete : ∀ transition, source transition →
    ∃ state, encode state = transition
  evaluatorValid : evaluator.validOnDomain source binding.obligation
  adequate : FormulaModel.validUnchecked
      (evaluator.on encode) binding.obligation → semantic

theorem TransitionFormulaAdequacy.valid {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {binding : CheckedPO theory project}
    {τ : Type u} {semantic : Prop} {source : CheckedBeforeAfter → Prop}
  (formula : TransitionFormulaAdequacy binding τ semantic source) :
    FormulaModel.validUnchecked
        (formula.evaluator.on formula.encode) binding.obligation :=
  formula.evaluator.validOnDomain_on source formula.encode
    binding.obligation formula.evaluatorValid formula.sourceValid

theorem TransitionFormulaAdequacy.sourceTransition
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {binding : CheckedPO theory project} {τ : Type u} {semantic : Prop}
    {source : CheckedBeforeAfter → Prop}
    (formula : TransitionFormulaAdequacy binding τ semantic source)
    (transition : CheckedBeforeAfter) (hsource : source transition) :
    ∃ state, formula.encode state = transition :=
  formula.sourceComplete transition hsource

theorem TransitionFormulaAdequacy.validWithCoverage
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {binding : CheckedPO theory project} {τ : Type u} {semantic : Prop}
    {source : CheckedBeforeAfter → Prop}
    (formula : TransitionFormulaAdequacy binding τ semantic source) :
    FormulaModel.validUnchecked
        (formula.evaluator.on formula.encode) binding.obligation ∧
      (∀ transition, source transition → ∃ state, formula.encode state = transition) :=
  ⟨formula.valid, formula.sourceComplete⟩

def invariantSemantic {σ : Type u} (event : Event σ) (invariant : σ → Prop) : Prop :=
  ∀ before after, invariant before → event.grd before → event.act before after →
    invariant after

def guardSemantic {γ α : Type u} (gluing : γ → α → Prop)
    (concrete : Event γ) (abstract : Event α) : Prop :=
  guardStrengthened gluing concrete abstract

def actionSemantic {γ α : Type u} (gluing : γ → α → Prop)
    (concrete : Event γ) (abstract : Event α) : Prop :=
  actionSimulates gluing concrete abstract

def feasibilitySemantic {σ : Type u} (pre : σ → Prop) (action : σ → σ → Prop) : Prop :=
  ∀ before, pre before → ∃ after, action before after

def witnessFeasibilitySemantic {σ α : Type u} (pre : σ → Prop)
    (predicate : σ → α → Prop) : Prop :=
  ∀ state, pre state → ∃ witness, predicate state witness

def witnessDefinednessSemantic {σ : Type u} (pre defined : σ → Prop) : Prop :=
  ∀ state, pre state → defined state

def implicationSemantic {σ : Type u} (hypotheses goal : σ → Prop) : Prop :=
  ∀ state, hypotheses state → goal state

/- A source-bound split conclusion names the selected abstract branch itself.
   `A.step` is intentionally not enough here: it could be discharged by an
   unrelated abstract event.  The positional `branchEvents` list is paired with
   `CheckedMergeSource.targets` by `MergeAdapter.branchLabelsExact`. -/
def splitSimulationSemantic {γ α : Type u} {C : Machine γ} {A : Machine α}
    {J : γ → α → Prop} (contract : SplitSimulation C A J)
    (branchEvents : List (String × Event α)) : Prop :=
  ∀ c c' a, J c a → contract.concreteEvent.grd c →
    contract.concreteEvent.act c c' →
      ∃ label branch a', (label, branch) ∈ branchEvents ∧
        branch.grd a ∧ branch.act a a' ∧ J c' a'

structure InvAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : CheckedPO theory project
  eventLabel : String
  invariantLabel : String
  kind : binding.obligation.kind = "INV"
  sourceName : binding.obligation.name = eventLabel ++ "/" ++ invariantLabel ++ "/INV"
  eventSource : CheckedEventSource theory project binding.obligation.component eventLabel
  guardSource : CheckedGuardSource theory project binding.obligation.component eventLabel
  event : Event σ
  invariant : σ → Prop
  fuel : Nat
  formula : TransitionFormulaAdequacy binding (σ × σ) (invariantSemantic event invariant)
    (eventSource.assignmentAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : eventActionExact eventSource fuel formula.encode
    (fun state => event.act state.1 state.2)
  guardExact : ∀ state, event.grd state.1 ↔
    guardSource.holds fuel (formula.encode state)
  nonempty : ∃ before after, event.grd before ∧ event.act before after

theorem InvAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ : Type u} (adapter : InvAdapter theory project σ) :
    invariantSemantic adapter.event adapter.invariant :=
  adapter.formula.adequate adapter.formula.valid

structure GrdAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (γ α : Type u) where
  binding : CheckedPO theory project
  concreteLabel : String
  abstractLabel : String
  kind : binding.obligation.kind = "GRD"
  sourceName : binding.obligation.name = concreteLabel ++ "/" ++ abstractLabel ++ "/GRD"
  eventSource : CheckedEventSource theory project binding.obligation.component concreteLabel
  guardSource : CheckedGuardSource theory project binding.obligation.component concreteLabel
  gluing : γ → α → Prop
  concrete : Event γ
  abstract : Event α
  fuel : Nat
  formula : TransitionFormulaAdequacy binding ((γ × γ) × α)
    (guardSemantic gluing concrete abstract)
    (eventSource.assignmentAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : eventActionExact eventSource fuel formula.encode
    (fun state => concrete.act state.1.1 state.1.2)
  guardExact : ∀ state, concrete.grd state.1.1 ↔
    guardSource.holds fuel (formula.encode state)
  nonempty : ∃ concreteState abstractState,
    gluing concreteState abstractState ∧ concrete.grd concreteState

theorem GrdAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {γ α : Type u} (adapter : GrdAdapter theory project γ α) :
    guardSemantic adapter.gluing adapter.concrete adapter.abstract :=
  adapter.formula.adequate adapter.formula.valid

structure SimAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (γ α : Type u) where
  binding : CheckedPO theory project
  concreteLabel : String
  abstractLabel : String
  kind : binding.obligation.kind = "SIM"
  sourceName : binding.obligation.name = concreteLabel ++ "/" ++ abstractLabel ++ "/SIM"
  eventSource : CheckedEventSource theory project binding.obligation.component concreteLabel
  guardSource : CheckedGuardSource theory project binding.obligation.component concreteLabel
  abstractSourceBound :
    EventB.POG.simSourceBound theory project binding.obligation.component concreteLabel
      abstractLabel binding.obligation = true
  gluing : γ → α → Prop
  concrete : Event γ
  abstract : Event α
  fuel : Nat
  formula : TransitionFormulaAdequacy binding ((γ × γ) × α)
    (actionSemantic gluing concrete abstract)
    (eventSource.assignmentAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : eventActionExact eventSource fuel formula.encode
    (fun state => concrete.act state.1.1 state.1.2)
  guardExact : ∀ state, concrete.grd state.1.1 ↔
    guardSource.holds fuel (formula.encode state)
  nonempty : ∃ concreteState concreteAfter abstractState,
    gluing concreteState abstractState ∧ concrete.grd concreteState ∧
      concrete.act concreteState concreteAfter

theorem SimAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {γ α : Type u} (adapter : SimAdapter theory project γ α) :
    actionSemantic adapter.gluing adapter.concrete adapter.abstract :=
  adapter.formula.adequate adapter.formula.valid

structure FisAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : CheckedPO theory project
  eventLabel : String
  actionLabel : String
  kind : binding.obligation.kind = "FIS"
  sourceName : binding.obligation.name = eventLabel ++ "/" ++ actionLabel ++ "/FIS"
  eventSource : CheckedRelationalEventSource theory project binding.obligation.component eventLabel
  pre : σ → Prop
  action : σ → σ → Prop
  fuel : Nat
  formula : TransitionFormulaAdequacy binding (σ × σ) (feasibilitySemantic pre action)
    (eventSource.relationAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : relationalEventActionExact eventSource fuel formula.encode
    (fun state => action state.1 state.2)
  nonempty : ∃ before, pre before

theorem FisAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ : Type u} (adapter : FisAdapter theory project σ) :
    feasibilitySemantic adapter.pre adapter.action :=
  adapter.formula.adequate adapter.formula.valid

structure WfisAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ α : Type u) where
  binding : CheckedPO theory project
  eventLabel : String
  witnessLabel : String
  kind : binding.obligation.kind = "WFIS"
  sourceName : binding.obligation.name = eventLabel ++ "/" ++ witnessLabel ++ "/WFIS"
  eventSource :
    CheckedWitnessSource theory project binding.obligation.component eventLabel witnessLabel
  sourcePredicate : EventB.Formula.Term
  sourcePredicateExact : sourcePredicate = eventSource.predicate
  pre : σ → Prop
  defined : σ → Prop
  predicate : σ → α → Prop
  contract : WitnessContract σ α pre defined predicate
  formula : FormulaAdequacy binding σ
    (witnessFeasibilitySemantic pre predicate)
  nonempty : ∃ state, pre state

theorem WfisAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ α : Type u} (adapter : WfisAdapter theory project σ α) :
    witnessFeasibilitySemantic adapter.pre adapter.predicate :=
  adapter.formula.adequate adapter.formula.valid

structure WwdAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ α : Type u) where
  binding : CheckedPO theory project
  eventLabel : String
  witnessLabel : String
  kind : binding.obligation.kind = "WWD"
  sourceName : binding.obligation.name = eventLabel ++ "/" ++ witnessLabel ++ "/WWD"
  eventSource :
    CheckedWitnessSource theory project binding.obligation.component eventLabel witnessLabel
  sourcePredicate : EventB.Formula.Term
  sourcePredicateExact : sourcePredicate = eventSource.predicate
  pre : σ → Prop
  defined : σ → Prop
  predicate : σ → α → Prop
  contract : WitnessContract σ α pre defined predicate
  formula : FormulaAdequacy binding σ
    (witnessDefinednessSemantic pre defined)

theorem WwdAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ α : Type u} (adapter : WwdAdapter theory project σ α) :
  witnessDefinednessSemantic adapter.pre adapter.defined :=
  adapter.formula.adequate adapter.formula.valid

structure VwdAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : CheckedPO theory project
  kind : binding.obligation.kind = "VWD"
  sourceName : binding.obligation.name = "VWD"
  variantSource : CheckedVariantSource project binding.obligation.component
  pre : σ → Prop
  defined : σ → Prop
  formula : FormulaAdequacy binding σ (witnessDefinednessSemantic pre defined)
  nonempty : ∃ state, pre state

theorem VwdAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ : Type u} (adapter : VwdAdapter theory project σ) :
    witnessDefinednessSemantic adapter.pre adapter.defined :=
  adapter.formula.adequate adapter.formula.valid

structure WdAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : CheckedPO theory project
  sourceLabel : String
  kind : binding.obligation.kind = "WD"
  sourceName : binding.obligation.name = sourceLabel ++ "/WD" ∨
    ∃ eventLabel, binding.obligation.name = eventLabel ++ "/" ++ sourceLabel ++ "/WD"
  pre : σ → Prop
  defined : σ → Prop
  formula : FormulaAdequacy binding σ (witnessDefinednessSemantic pre defined)

theorem WdAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ : Type u} (adapter : WdAdapter theory project σ) :
    witnessDefinednessSemantic adapter.pre adapter.defined :=
  adapter.formula.adequate adapter.formula.valid

structure ThmAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : CheckedPO theory project
  sourceLabel : String
  kind : binding.obligation.kind = "THM"
  sourceName : binding.obligation.name = sourceLabel ++ "/THM"
  hypotheses : σ → Prop
  goal : σ → Prop
  formula : FormulaAdequacy binding σ (implicationSemantic hypotheses goal)

theorem ThmAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {σ : Type u} (adapter : ThmAdapter theory project σ) :
    implicationSemantic adapter.hypotheses adapter.goal :=
  adapter.formula.adequate adapter.formula.valid

structure MergeAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) {γ α : Type u}
    {C : Machine γ} {A : Machine α} (J : γ → α → Prop) where
  binding : CheckedPO theory project
  eventLabel : String
  kind : binding.obligation.kind = "MRG"
  sourceName : binding.obligation.name = eventLabel ++ "/MRG"
  eventSource : CheckedEventSource theory project binding.obligation.component eventLabel
  mergeSource : CheckedMergeSource theory project binding.obligation.component eventLabel
  guardSource : CheckedGuardSource theory project binding.obligation.component eventLabel
  contract : SplitSimulation C A J
  branchBindings : List (CheckedMergeBranch theory project α)
  branchBindingLocatorsExact :
    branchBindings.map (·.locator) = mergeSource.targetLocators
  branchBindingObjectsExact :
    contract.abstractEvents = branchBindings.map (·.event)
  branchEvents : List (String × Event α)
  branchLabelsExact : branchEvents.map (·.1) = mergeSource.targets
  branchObjectsExact : contract.abstractEvents = branchEvents.map (·.2)
  branchBindingEventsExact :
    branchEvents = branchBindings.map (fun branch => (branch.locator.2, branch.event))
  fuel : Nat
  formula : TransitionFormulaAdequacy binding ((γ × γ) × α)
    (splitSimulationSemantic contract branchEvents) (eventSource.assignmentAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : eventActionExact eventSource fuel formula.encode
    (fun state => contract.concreteEvent.act state.1.1 state.1.2)
  guardExact : ∀ state, contract.concreteEvent.grd state.1.1 ↔
    guardSource.holds fuel (formula.encode state)

theorem MergeAdapter.sound {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {γ α : Type u} {C : Machine γ} {A : Machine α} {J : γ → α → Prop}
    (adapter : MergeAdapter (C := C) (A := A) theory project J) :
  ∀ c c' a, J c a → adapter.contract.concreteEvent.grd c →
    adapter.contract.concreteEvent.act c c' →
      ∃ label branch a', (label, branch) ∈ adapter.branchEvents ∧
        branch.grd a ∧ branch.act a a' ∧ J c' a' := by
  exact adapter.formula.adequate adapter.formula.valid

structure IntegerVariantAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  natBinding : CheckedPO theory project
  varBinding : CheckedPO theory project
  natKind : natBinding.obligation.kind = "NAT"
  varKind : varBinding.obligation.kind = "VAR"
  componentMatch : varBinding.obligation.component = natBinding.obligation.component
  eventLabel : String
  eventSource : CheckedEventSource theory project natBinding.obligation.component eventLabel
  variantSource : CheckedVariantSource project natBinding.obligation.component
  natName : natBinding.obligation.name = eventLabel ++ "/NAT"
  varName : varBinding.obligation.name = eventLabel ++ "/VAR"
  contract : IntegerVariant σ
  sourceMatch : contract.source = eventLabel
  fuel : Nat
  natFormula : TransitionFormulaAdequacy natBinding (σ × σ)
    (integerVariantNaturality contract) (eventSource.assignmentAction fuel)
  varFormula : TransitionFormulaAdequacy varBinding (σ × σ)
    (integerVariantProgressSemantic contract) (eventSource.assignmentAction fuel)
  fuelExact : natFormula.evaluator.fuel = fuel ∧ varFormula.evaluator.fuel = fuel
  natActionExact : eventActionExact eventSource fuel natFormula.encode
    (fun state => contract.action state.1 state.2)
  varActionExact : eventActionExact eventSource fuel varFormula.encode
    (fun state => contract.action state.1 state.2)

theorem IntegerVariantAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u}
    (adapter : IntegerVariantAdapter theory project σ) :
    integerVariantNaturality adapter.contract ∧
      integerVariantProgressSemantic adapter.contract :=
  ⟨adapter.natFormula.adequate adapter.natFormula.valid,
    adapter.varFormula.adequate adapter.varFormula.valid⟩

structure NaturalVariantAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  natBinding : CheckedPO theory project
  varBinding : CheckedPO theory project
  natKind : natBinding.obligation.kind = "NAT"
  varKind : varBinding.obligation.kind = "VAR"
  componentMatch : varBinding.obligation.component = natBinding.obligation.component
  eventLabel : String
  eventSource : CheckedEventSource theory project natBinding.obligation.component eventLabel
  variantSource : CheckedVariantSource project natBinding.obligation.component
  natName : natBinding.obligation.name = eventLabel ++ "/NAT"
  varName : varBinding.obligation.name = eventLabel ++ "/VAR"
  measure : σ → Nat
  action : σ → σ → Prop
  fuel : Nat
  natFormula : TransitionFormulaAdequacy natBinding (σ × σ) (∀ state, 0 ≤ measure state)
    (eventSource.assignmentAction fuel)
  varFormula : TransitionFormulaAdequacy varBinding (σ × σ)
    (∀ before after, action before after → measure after < measure before)
    (eventSource.assignmentAction fuel)
  fuelExact : natFormula.evaluator.fuel = fuel ∧ varFormula.evaluator.fuel = fuel
  natActionExact : eventActionExact eventSource fuel natFormula.encode
    (fun state => action state.1 state.2)
  varActionExact : eventActionExact eventSource fuel varFormula.encode
    (fun state => action state.1 state.2)

theorem NaturalVariantAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u}
    (adapter : NaturalVariantAdapter theory project σ) :
    (∀ state, 0 ≤ adapter.measure state) ∧
      (∀ before after, adapter.action before after →
        adapter.measure after < adapter.measure before) :=
  ⟨adapter.natFormula.adequate adapter.natFormula.valid,
    adapter.varFormula.adequate adapter.varFormula.valid⟩

/-- Source-bound VAR adapter for variants whose well-founded order is supplied by
    the semantic model rather than guessed from the surface expression. -/
structure WellFoundedVariantAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) (α : Type v)
    (contract : WellFoundedVariant σ α) where
  binding : CheckedPO theory project
  kind : binding.obligation.kind = "VAR"
  eventLabel : String
  sourceName : binding.obligation.name = eventLabel ++ "/VAR"
  eventSource : CheckedEventSource theory project binding.obligation.component eventLabel
  variantSource : CheckedVariantSource project binding.obligation.component
  fuel : Nat
  formula : TransitionFormulaAdequacy binding (σ × σ)
    (wellFoundedVariantProgressSemantic contract)
    (eventSource.assignmentAction fuel)
  fuelExact : formula.evaluator.fuel = fuel
  actionExact : eventActionExact eventSource fuel formula.encode
    (fun state => contract.action state.1 state.2)

theorem WellFoundedVariantAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u} {α : Type v}
    {contract : WellFoundedVariant σ α}
    (adapter : WellFoundedVariantAdapter theory project σ α contract) :
    wellFoundedVariantProgressSemantic contract :=
  adapter.formula.adequate adapter.formula.valid

structure FiniteSetVariantAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) {σ : Type u} {α : Type v} {γ : Type u}
    (contract : FiniteSetVariant σ α) where
  finBinding : CheckedPO theory project
  varBinding : CheckedPO theory project
  finKind : finBinding.obligation.kind = "FIN"
  varKind : varBinding.obligation.kind = "VAR"
  componentMatch : varBinding.obligation.component = finBinding.obligation.component
  eventLabel : String
  eventSource : CheckedEventSource theory project finBinding.obligation.component eventLabel
  variantSource : CheckedVariantSource project finBinding.obligation.component
  finName : finBinding.obligation.name = "FIN"
  varName : varBinding.obligation.name = eventLabel ++ "/VAR"
  convergence : String
  convergenceExact :
    EventB.POG.eventConvergenceMode? project finBinding.obligation.component eventLabel =
      some convergence
  modeExact : match contract.mode with
    | .anticipated => convergence = "2"
    | .convergent => convergence = "1"
  fuel : Nat
  stateOf : γ → σ
  stateCoverage : ∀ state, ∃ encoded, stateOf encoded = state
  finFormula : FormulaAdequacy finBinding σ (finiteVariantFiniteness contract)
  varFormula : TransitionFormulaAdequacy varBinding (γ × γ)
    (∀ state : γ × γ,
      contract.action (stateOf state.1) (stateOf state.2) →
        finiteVariantProgress contract.mode
          (contract.measure (stateOf state.2)) (contract.measure (stateOf state.1)))
    (eventSource.assignmentAction fuel)
  decodeVariantValue : Value → Option α
  measureExact : ∀ state,
    match evalValueAtFuel fuel (finFormula.encode state) variantSource.expression with
    | .ok (.set values) => values.mapM decodeVariantValue = some (contract.measure state)
    | _ => False
  fuelExact : finFormula.evaluator.fuel = fuel ∧ varFormula.evaluator.fuel = fuel
  varActionExact : eventActionExact eventSource fuel varFormula.encode
    (fun state : γ × γ => contract.action (stateOf state.1) (stateOf state.2))

theorem FiniteSetVariantAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u} {α : Type v} {γ : Type u}
    {contract : FiniteSetVariant σ α}
    (adapter : FiniteSetVariantAdapter (γ := γ) theory project contract) :
  finiteVariantFiniteness contract ∧ finiteVariantProgressSemantic contract :=
  ⟨adapter.finFormula.adequate adapter.finFormula.valid, by
    intro before after action
    obtain ⟨before', beforeEq⟩ := adapter.stateCoverage before
    obtain ⟨after', afterEq⟩ := adapter.stateCoverage after
    have stateAction : contract.action (adapter.stateOf before') (adapter.stateOf after') := by
      simpa [beforeEq, afterEq] using action
    have encodedAction :=
      (adapter.varFormula.adequate adapter.varFormula.valid) (before', after') stateAction
    simpa [beforeEq, afterEq] using encodedAction⟩

/- Restricted finite variants use an explicit semantic state domain and a source-indexed
   VAR carrier. Unlike the legacy adapter above, the VAR formula is not quantified over
   every semantic pair; only states in `η` whose encoding is a checked source transition
   are admitted. -/
structure RestrictedFiniteSetVariantAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) {σ : Type u} {α : Type v} {γ : Type u}
    {η : Type u} (contract : FiniteSetVariant σ α) where
  finBinding : CheckedPO theory project
  varBinding : CheckedPO theory project
  finKind : finBinding.obligation.kind = "FIN"
  varKind : varBinding.obligation.kind = "VAR"
  componentMatch : varBinding.obligation.component = finBinding.obligation.component
  eventLabel : String
  eventSource : CheckedEventSource theory project finBinding.obligation.component eventLabel
  variantSource : CheckedVariantSource project finBinding.obligation.component
  finName : finBinding.obligation.name = "FIN"
  varName : varBinding.obligation.name = eventLabel ++ "/VAR"
  convergence : String
  convergenceExact :
    EventB.POG.eventConvergenceMode? project finBinding.obligation.component eventLabel =
      some convergence
  modeExact : match contract.mode with
    | .anticipated => convergence = "2"
    | .convergent => convergence = "1"
  fuel : Nat
  stateOf : γ → σ
  stateCoverage : ∀ state, ∃ encoded, stateOf encoded = state
  finGoalExact : finBinding.obligation.goal =
    some (.app (.id "finite") variantSource.expression)
  semanticDomain : ValueEnv → Prop
  finFormula : DomainFormulaAdequacy finBinding σ
    (finiteVariantFiniteness contract)
    semanticDomain
  finitenessExact : ∀ state,
    contract.finite state ↔
      finFormula.evaluator.denote
        (.app (.id "finite") variantSource.expression)
        (finFormula.encode state)
  varState : Type u
  varBefore : varState → γ
  varAfter : varState → γ
  /-- The source relation may restrict checked event transitions to the invariant
      domain represented by `semanticDomain`. -/
  varSource : CheckedBeforeAfter → Prop
  varSourceExact : ∀ transition,
    varSource transition ↔
      eventSource.assignmentAction fuel transition ∧
        semanticDomain transition.before ∧ semanticDomain transition.after
  varFormula : TransitionFormulaAdequacy varBinding varState
    (∀ state : varState,
      contract.action (stateOf (varBefore state)) (stateOf (varAfter state)) →
        finiteVariantProgress contract.mode
          (contract.measure (stateOf (varAfter state)))
          (contract.measure (stateOf (varBefore state))))
    varSource
  varPairCoverage : ∀ before after,
    contract.action (stateOf before) (stateOf after) →
      ∃ state, varBefore state = before ∧ varAfter state = after
  varActionExact : ∀ state,
    contract.action (stateOf (varBefore state)) (stateOf (varAfter state)) ↔
      varSource (varFormula.encode state)
  fuelExact : finFormula.evaluator.fuel = fuel ∧ varFormula.evaluator.fuel = fuel

theorem RestrictedFiniteSetVariantAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u} {α : Type v} {γ : Type u}
    {η : Type u} {contract : FiniteSetVariant σ α}
    (adapter : RestrictedFiniteSetVariantAdapter (η := η) (γ := γ)
      theory project contract) :
    finiteVariantFiniteness contract ∧ finiteVariantProgressSemantic contract := by
  constructor
  · exact adapter.finFormula.adequate adapter.finFormula.valid
  · intro before after action
    obtain ⟨before', beforeEq⟩ := adapter.stateCoverage before
    obtain ⟨after', afterEq⟩ := adapter.stateCoverage after
    have stateAction : contract.action (adapter.stateOf before')
        (adapter.stateOf after') := by
      simpa [beforeEq, afterEq] using action
    obtain ⟨state, beforeStateEq, afterStateEq⟩ :=
      adapter.varPairCoverage before' after' stateAction
    have stateAction' : contract.action (adapter.stateOf (adapter.varBefore state))
        (adapter.stateOf (adapter.varAfter state)) := by
      simpa [beforeStateEq, afterStateEq] using stateAction
    have progress := (adapter.varFormula.adequate adapter.varFormula.valid) state stateAction'
    simpa [beforeEq, afterEq, beforeStateEq, afterStateEq] using progress

/- The current VAR carrier is deliberately diagnosed here: surjective semantic-state
   coverage plus source validity and action exactness forces every semantic pair to be
   an Event-B source transition.  This is acceptable for the constant fixture, but it
   prevents a non-total state-dependent finite-set action from inhabiting the adapter. -/
theorem FiniteSetVariantAdapter.actionTotal {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u} {α : Type v} {γ : Type u}
    {contract : FiniteSetVariant σ α}
    (adapter : FiniteSetVariantAdapter (γ := γ) theory project contract) :
    ∀ before after, contract.action before after := by
  intro before after
  obtain ⟨before', beforeEq⟩ := adapter.stateCoverage before
  obtain ⟨after', afterEq⟩ := adapter.stateCoverage after
  have source := adapter.varFormula.sourceValid (before', after')
  have action := (adapter.varActionExact (before', after')).mpr source
  simpa [beforeEq, afterEq] using action

/- The source equalities are intentionally redundant with the names above: they make
   the NAT/VAR pairing a checked identity, rather than a caller convention. -/
def finiteVariantSourceMatch (source : String) (nat var : Obligation) : Bool :=
  nat.kind == "NAT" && var.kind == "VAR" &&
    nat.name == source ++ "/NAT" && var.name == source ++ "/VAR"

def finiteSetVariantSourceMatch (source : String) (fin var : Obligation) : Bool :=
  fin.kind == "FIN" && var.kind == "VAR" &&
    fin.name == "FIN" && var.name == source ++ "/VAR"

#guard finiteVariantSourceMatch "step"
  { name := "step/NAT", kind := "NAT" }
  { name := "step/VAR", kind := "VAR" }
#guard !finiteVariantSourceMatch "step"
  { name := "other/NAT", kind := "NAT" }
  { name := "step/VAR", kind := "VAR" }

private def finiteVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [ ("org.eventb.core.name", "M") ]
       [ .variable [ ("org.eventb.core.identifier", "x") ] []
       , .invariant [ ("org.eventb.core.label", "type")
                    , ("org.eventb.core.predicate", "x ∈ ℤ") ] []
       , .variant [ ("org.eventb.core.expression", "x") ] []
       , .event [ ("org.eventb.core.label", "INITIALISATION") ]
           [ .action [ ("org.eventb.core.label", "set")
                     , ("org.eventb.core.assignment", "x ≔ 0") ] [] ]
       , .event [ ("org.eventb.core.label", "step")
                , ("org.eventb.core.convergence", "1") ]
           [ .action [ ("org.eventb.core.label", "set")
                     , ("org.eventb.core.assignment", "x ≔ x") ] [] ] ] }]

private def theoremFixtureProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .invariant [("org.eventb.core.label", "taut"),
                    ("org.eventb.core.theorem", "true"),
                    ("org.eventb.core.predicate", "1 = 1")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [] ] }]

#guard match generateCheckedIn EventB.Theory.empty theoremFixtureProject "M" with
  | .ok obligations =>
      match obligations.find? (fun obligation => obligation.kind == "THM") with
      | some thm => thm.name == "taut/THM" &&
          Obligation.sourceBound theoremFixtureProject thm
      | none => false
  | .error _ => false

#guard (CheckedPO.fromGenerated? EventB.Theory.empty theoremFixtureProject "M"
  (fun obligation => obligation.kind == "THM" && obligation.name == "taut/THM")).isSome

private def positiveThmObligation : Obligation :=
  { component := "M", name := "taut/THM", kind := "THM"
    goal := some (.bin "=" (.num 1) (.num 1)) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty theoremFixtureProject
  positiveThmObligation).isSome

private def positiveThmPO : CheckedPO EventB.Theory.empty theoremFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty theoremFixtureProject
    positiveThmObligation).get (by native_decide)

private theorem positiveThmPO_obligation :
    positiveThmPO.obligation = positiveThmObligation := by
  native_decide

private abbrev theoremState :=
  { env : ValueEnv // ValueEnv.validationOk 128 [] env = true }

private def positiveThmAdapter :
    ThmAdapter EventB.Theory.empty theoremFixtureProject theoremState :=
  { binding := positiveThmPO
    sourceLabel := "taut"
    kind := by native_decide
    sourceName := by native_decide
    hypotheses := fun _ => True
    goal := fun _ => True
    formula :=
      { evaluator := constantTypedFormulaModel
        encode := fun state => state.1
        declarationScope := none
        declarationsBound := by
          have component : positiveThmPO.obligation.component = "M" := by native_decide
          rw [component]
          change exactComponentDeclarations? EventB.Theory.empty theoremFixtureProject "M" = some []
          native_decide
        stateValid := by
          intro state
          exact state.2
        stateComplete := by
          intro env h
          exact ⟨⟨env, h⟩, rfl⟩
        evaluatorValid := by
          rw [positiveThmPO_obligation]
          exact constantTypedFormulaModel_taut_valid
        adequate := by
          intro _ _ _
          trivial } }

example : implicationSemantic positiveThmAdapter.hypotheses positiveThmAdapter.goal :=
  positiveThmAdapter.sound

private def invariantFixtureProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .invariant [("org.eventb.core.label", "taut"),
                    ("org.eventb.core.predicate", "1 = 1")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] [] ] }]

private def positiveInvObligation : Obligation :=
  { component := "M", name := "INITIALISATION/taut/INV", kind := "INV"
    goal := some (.bin "=" (.num 1) (.num 1)) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty invariantFixtureProject
  positiveInvObligation).isSome

private def positiveInvPO : CheckedPO EventB.Theory.empty invariantFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty invariantFixtureProject
    positiveInvObligation).get (by native_decide)

private theorem positiveInvPO_obligation :
    positiveInvPO.obligation = positiveInvObligation := by
  native_decide

private def invariantFixtureSource : CheckedEventSource EventB.Theory.empty
    invariantFixtureProject "M" "INITIALISATION" :=
  (CheckedEventSource.fromProject EventB.Theory.empty invariantFixtureProject "M"
    "INITIALISATION").get (by native_decide)

private def invariantFixtureTransition : CheckedBeforeAfter :=
  { before := {}, after := {}, declarations := [] }

private theorem invariantFixtureAssignment :
    assignmentRelation 128 [] invariantFixtureTransition [] := by
  constructor
  · rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

private def positiveInvSource : CheckedEventSource EventB.Theory.empty
    invariantFixtureProject positiveInvPO.obligation.component "INITIALISATION" := by
  have component : positiveInvPO.obligation.component = "M" := by native_decide
  rw [component]
  exact invariantFixtureSource

private def positiveInvGuardSource : CheckedGuardSource EventB.Theory.empty
    invariantFixtureProject positiveInvPO.obligation.component "INITIALISATION" := by
  have component : positiveInvPO.obligation.component = "M" := by native_decide
  rw [component]
  exact (CheckedGuardSource.fromProject EventB.Theory.empty invariantFixtureProject
    "M" "INITIALISATION").get (by native_decide)

private abbrev invariantSourceState :=
  { transition : CheckedBeforeAfter //
      positiveInvSource.assignmentAction 128 transition }

private def invariantSourceModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := positiveInvSource.assignmentAction 128
    inhabited := ⟨invariantFixtureTransition, by
      change assignmentRelation 128 positiveInvSource.declarations
        invariantFixtureTransition positiveInvSource.updates
      have declarations : positiveInvSource.declarations = [] := by native_decide
      have updates : positiveInvSource.updates = [] := by native_decide
      rw [declarations, updates]
      exact invariantFixtureAssignment⟩
    supports := fun _ => true }

private def positiveInvAdapter : InvAdapter EventB.Theory.empty invariantFixtureProject
    invariantSourceState :=
  { binding := positiveInvPO
    eventLabel := "INITIALISATION"
    invariantLabel := "taut"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveInvSource
    guardSource := positiveInvGuardSource
    event := { grd := fun _ => True, act := fun _ _ => True }
    invariant := fun _ => True
    formula :=
      { evaluator := invariantSourceModel
        encode := fun state => state.1.1
        declarations := []
        declarationScope := some "INITIALISATION"
        declarationsBound := by
          have component : positiveInvPO.obligation.component = "M" := by native_decide
          rw [component]
          change exactEventDeclarations? EventB.Theory.empty invariantFixtureProject "M"
            "INITIALISATION" = some []
          native_decide
        transitionDeclarations := by
          intro state
          change state.1.1.declarations = []
          have declarations : positiveInvSource.declarations = [] := by native_decide
          rcases state.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
          simpa [declarations] using declared
        transitionValid := by intro state; exact state.1.2
        sourceValid := by intro state; exact state.1.2
        sourceComplete := by
          intro transition h
          exact ⟨(⟨transition, h⟩, ⟨transition, h⟩), rfl⟩
        evaluatorValid := by
          set_option maxRecDepth 100000 in
          simpa only [positiveInvPO_obligation] using
            (typedTransitionModel_taut_validOnDomain invariantSourceModel
              (positiveInvSource.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, assigned⟩
                constructor
                · simpa [declared] using beforeValid
                · simpa [declared] using afterValid)
              positiveInvObligation (by native_decide) (by native_decide)
              (by native_decide) (by native_decide) (by rfl)
              (by intro _; rfl))
        adequate := by
          intro _
          intro before after _ _ _
          trivial }
    fuel := 128
    fuelExact := by rfl
    actionExact := by
      intro state
      constructor
      · intro _
        exact state.1.2
      · intro _
        trivial
    guardExact := by
      intro state
      have declarations : positiveInvGuardSource.declarations = [] := by native_decide
      have predicates : positiveInvGuardSource.predicates = [] := by native_decide
      have source : positiveInvSource.declarations = [] := by native_decide
      rcases state.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
      constructor
      · intro _
        unfold CheckedGuardSource.holds
        rw [declarations, predicates]
        constructor
        · simpa [source] using declared
        constructor
        · simpa [source] using beforeValid
        constructor
        · simpa [source] using afterValid
        · simp
      · intro _
        trivial
    nonempty := by
      let state : invariantSourceState := ⟨invariantFixtureTransition, by
        change assignmentRelation 128 positiveInvSource.declarations
          invariantFixtureTransition positiveInvSource.updates
        have declarations : positiveInvSource.declarations = [] := by native_decide
        have updates : positiveInvSource.updates = [] := by native_decide
        rw [declarations, updates]
        exact invariantFixtureAssignment⟩
      exact ⟨state, state, trivial, trivial⟩ }

example : invariantSemantic positiveInvAdapter.event positiveInvAdapter.invariant :=
  positiveInvAdapter.sound

private def grdFixtureProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [ .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "step")]
           [ .guard [("org.eventb.core.label", "g"),
                     ("org.eventb.core.predicate", "1 = 1")] [] ] ] }
   , { name := "C"
       elem := .machineFile [("org.eventb.core.name", "C")]
         [ .refinesMachine [("org.eventb.core.target", "A")] []
         , .event [("org.eventb.core.label", "INITIALISATION")] []
         , .event [("org.eventb.core.label", "step")]
             [ .refinesEvent [("org.eventb.core.target", "A/step")] [] ] ] }]

#guard match generateCheckedIn EventB.Theory.empty grdFixtureProject "C" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.kind == "GRD" && obligation.name == "step/g/GRD")
  | .error _ => false

private def positiveGrdObligation : Obligation :=
  { component := "C", name := "step/g/GRD", kind := "GRD"
    goal := some (.bin "=" (.num 1) (.num 1)) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty grdFixtureProject
  positiveGrdObligation).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty grdFixtureProject
  { positiveGrdObligation with goal := some (.bin "=" (.num 1) (.num 2)) }).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty grdFixtureProject
  { positiveGrdObligation with component := "A" }).isSome

private def positiveGrdPO : CheckedPO EventB.Theory.empty grdFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty grdFixtureProject
    positiveGrdObligation).get (by native_decide)

private def positiveGrdSource : CheckedEventSource EventB.Theory.empty
    grdFixtureProject positiveGrdPO.obligation.component "step" := by
  have component : positiveGrdPO.obligation.component = "C" := by native_decide
  rw [component]
  exact (CheckedEventSource.fromProject EventB.Theory.empty grdFixtureProject "C" "step").get
    (by native_decide)

private def positiveGrdGuardSource : CheckedGuardSource EventB.Theory.empty
    grdFixtureProject positiveGrdPO.obligation.component "step" := by
  have component : positiveGrdPO.obligation.component = "C" := by native_decide
  rw [component]
  exact (CheckedGuardSource.fromProject EventB.Theory.empty grdFixtureProject
    "C" "step").get (by native_decide)

private abbrev grdSourceState :=
  { transition : CheckedBeforeAfter //
      positiveGrdSource.assignmentAction 128 transition }

private def grdSourceModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := positiveGrdSource.assignmentAction 128
    inhabited := ⟨invariantFixtureTransition, by
      change assignmentRelation 128 positiveGrdSource.declarations
        invariantFixtureTransition positiveGrdSource.updates
      have declarations : positiveGrdSource.declarations = [] := by native_decide
      have updates : positiveGrdSource.updates = [] := by native_decide
      rw [declarations, updates]
      exact invariantFixtureAssignment⟩
    supports := fun _ => true }

private def positiveGrdAdapter : GrdAdapter EventB.Theory.empty grdFixtureProject
    grdSourceState Unit :=
  { binding := positiveGrdPO
    concreteLabel := "step"
    abstractLabel := "g"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveGrdSource
    guardSource := positiveGrdGuardSource
    gluing := fun _ _ => True
    concrete :=
      { grd := fun _ => True
        act := fun before _ => positiveGrdSource.assignmentAction 128 before.1 }
    abstract := { grd := fun _ => True, act := fun _ _ => True }
    formula :=
      { evaluator := grdSourceModel
        encode := fun state => state.1.1.1
        declarations := []
        declarationScope := some "step"
        declarationsBound := by
          have component : positiveGrdPO.obligation.component = "C" := by native_decide
          rw [component]
          change exactEventDeclarations? EventB.Theory.empty grdFixtureProject "C" "step" = some []
          native_decide
        transitionDeclarations := by
          intro state
          change state.1.1.1.declarations = []
          have declarations : positiveGrdSource.declarations = [] := by native_decide
          rcases state.1.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
          simpa [declarations] using declared
        transitionValid := by intro state; exact state.1.1.2
        sourceValid := by intro state; exact state.1.1.2
        sourceComplete := by
          intro transition h
          exact ⟨((⟨transition, h⟩, ⟨transition, h⟩), ()), rfl⟩
        evaluatorValid := by
          set_option maxRecDepth 100000 in
          simpa only [show positiveGrdPO.obligation = positiveGrdObligation by native_decide] using
            (typedTransitionModel_taut_validOnDomain grdSourceModel
              (positiveGrdSource.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, assigned⟩
                constructor
                · simpa [declared] using beforeValid
                · simpa [declared] using afterValid)
              positiveGrdObligation (by native_decide) (by native_decide)
              (by native_decide) (by native_decide) (by rfl)
              (by intro _; rfl))
        adequate := by
          intro _
          intro concrete abstract _ _
          trivial }
    fuel := 128
    fuelExact := by rfl
    actionExact := by intro _; exact Iff.rfl
    guardExact := by
      intro state
      have declarations : positiveGrdGuardSource.declarations = [] := by native_decide
      have predicates : positiveGrdGuardSource.predicates = [] := by native_decide
      have source : positiveGrdSource.declarations = [] := by native_decide
      rcases state.1.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
      constructor
      · intro _
        unfold CheckedGuardSource.holds
        rw [declarations, predicates]
        constructor
        · simpa [source] using declared
        constructor
        · simpa [source] using beforeValid
        constructor
        · simpa [source] using afterValid
        · simp
      · intro _
        trivial
    nonempty := by
      let state : grdSourceState := ⟨invariantFixtureTransition, by
        change assignmentRelation 128 positiveGrdSource.declarations
          invariantFixtureTransition positiveGrdSource.updates
        have declarations : positiveGrdSource.declarations = [] := by native_decide
        have updates : positiveGrdSource.updates = [] := by native_decide
        rw [declarations, updates]
        exact invariantFixtureAssignment⟩
      exact ⟨state, (), trivial, trivial⟩ }

example : guardSemantic positiveGrdAdapter.gluing
    positiveGrdAdapter.concrete positiveGrdAdapter.abstract :=
  positiveGrdAdapter.sound

private def simFixtureProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 0")] [] ]
       , .event [("org.eventb.core.label", "step")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 1")] [] ] ] }
   , { name := "C"
       elem := .machineFile [("org.eventb.core.name", "C")]
         [ .refinesMachine [("org.eventb.core.target", "A")] []
         , .variable [("org.eventb.core.identifier", "x")] []
         , .event [("org.eventb.core.label", "INITIALISATION")]
             [ .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ 0")] [] ]
         , .event [("org.eventb.core.label", "step")]
             [ .refinesEvent [("org.eventb.core.target", "A/step")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ 1")] [] ] ] }]

private def positiveSimObligation : Obligation :=
  { component := "C", name := "step/set/SIM", kind := "SIM"
    hyps := []
    goal := some (.bin "=" (.num 1) (.num 1)) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty simFixtureProject
  positiveSimObligation).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty simFixtureProject
  { positiveSimObligation with goal := some (.bin "=" (.id "x") (.num 1)) }).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty simFixtureProject
  { positiveSimObligation with component := "A" }).isSome

private def positiveSimPO : CheckedPO EventB.Theory.empty simFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty simFixtureProject
    positiveSimObligation).get (by native_decide)

private def positiveSimSource : CheckedEventSource EventB.Theory.empty
    simFixtureProject positiveSimPO.obligation.component "step" := by
  have component : positiveSimPO.obligation.component = "C" := by native_decide
  rw [component]
  exact (CheckedEventSource.fromProject EventB.Theory.empty simFixtureProject "C" "step").get
    (by native_decide)

private def positiveSimGuardSource : CheckedGuardSource EventB.Theory.empty
    simFixtureProject positiveSimPO.obligation.component "step" := by
  have component : positiveSimPO.obligation.component = "C" := by native_decide
  rw [component]
  exact (CheckedGuardSource.fromProject EventB.Theory.empty simFixtureProject
    "C" "step").get (by native_decide)

private def simFixtureTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 1)] }
    after := { values := [("x", .integer 1)] }
    declarations := [("x", .int)] }

private theorem simFixtureAssignment :
    assignmentRelation 128 [("x", .int)] simFixtureTransition [("x", .num 1)] := by
  exact assignmentRelation_x_one

private abbrev simSourceState :=
  { transition : CheckedBeforeAfter //
      positiveSimSource.assignmentAction 128 transition }

private def simFixtureState : simSourceState := ⟨simFixtureTransition, by
  change assignmentRelation 128 positiveSimSource.declarations
    simFixtureTransition positiveSimSource.updates
  have declarations : positiveSimSource.declarations = [("x", .int)] := by
    native_decide
  have updates : positiveSimSource.updates = [("x", .num 1)] := by
    native_decide
  rw [declarations, updates]
  exact simFixtureAssignment⟩

private def simSourceModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := positiveSimSource.assignmentAction 128
    inhabited := ⟨simFixtureTransition, simFixtureState.property⟩
    supports := fun _ => true }

private def positiveSimAdapter : SimAdapter EventB.Theory.empty simFixtureProject
    simSourceState Unit :=
  { binding := positiveSimPO
    concreteLabel := "step"
    abstractLabel := "set"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveSimSource
    guardSource := positiveSimGuardSource
    abstractSourceBound := by native_decide
    gluing := fun _ _ => True
    concrete :=
      { grd := fun _ => True
        act := fun before _ => positiveSimSource.assignmentAction 128 before.1 }
    abstract := { grd := fun _ => True, act := fun _ _ => True }
    formula :=
      { evaluator := simSourceModel
        encode := fun state => state.1.1.1
        declarations := [("x", .int)]
        declarationScope := some "step"
        declarationsBound := by
          have component : positiveSimPO.obligation.component = "C" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty simFixtureProject "C" "step" =
            some [("x", .int)]
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.1.2 with ⟨declared, _, _, _⟩
          have sourceDeclarations : positiveSimSource.declarations = [("x", .int)] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by
          intro state
          exact state.1.1.2
        sourceValid := by
          intro state
          exact state.1.1.2
        sourceComplete := by
          intro transition source
          exact ⟨((⟨transition, source⟩, simFixtureState), ()), rfl⟩
        evaluatorValid := by
          set_option maxRecDepth 100000 in
          simpa only [show positiveSimPO.obligation = positiveSimObligation by native_decide] using
            (typedTransitionModel_taut_validOnDomain simSourceModel
              (positiveSimSource.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, assigned⟩
                constructor
                · simpa [declared] using beforeValid
                · simpa [declared] using afterValid)
              positiveSimObligation (by native_decide) (by native_decide)
              (by native_decide) (by native_decide) (by rfl)
              (by intro _; rfl))
        adequate := by
          intro _ c c' a _ _ _
          exact ⟨a, trivial, trivial⟩ }
    fuel := 128
    fuelExact := by rfl
    actionExact := by
      intro state
      exact Iff.rfl
    guardExact := by
      intro state
      have declarations : positiveSimGuardSource.declarations = [("x", .int)] := by
        native_decide
      have predicates : positiveSimGuardSource.predicates = [] := by native_decide
      have source : positiveSimSource.declarations = [("x", .int)] := by native_decide
      rcases state.1.1.2 with ⟨declared, beforeValid, afterValid, assigned⟩
      constructor
      · intro _
        unfold CheckedGuardSource.holds
        rw [declarations, predicates]
        constructor
        · simpa [source] using declared
        constructor
        · simpa [source] using beforeValid
        constructor
        · simpa [source] using afterValid
        · simp
      · intro _
        trivial
    nonempty := by
      exact ⟨simFixtureState, simFixtureState, (), trivial, trivial,
        simFixtureState.property⟩ }

example : actionSemantic positiveSimAdapter.gluing
    positiveSimAdapter.concrete positiveSimAdapter.abstract :=
  positiveSimAdapter.sound

/- Nondeterministic actions use the relational source binder below. -/

private def nondeterministicFixtureProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "x ∈ ℤ")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "choose"),
                      ("org.eventb.core.assignment", "x :∈ {0}")] [] ] ] }]

#guard match generateCheckedIn EventB.Theory.empty nondeterministicFixtureProject "M" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.kind == "FIS" && obligation.name == "INITIALISATION/choose/FIS")
  | .error _ => false
#guard (CheckedEventSource.fromProject EventB.Theory.empty nondeterministicFixtureProject
  "M" "INITIALISATION").isNone

private def positiveFisObligation : Obligation :=
  { component := "M", name := "INITIALISATION/choose/FIS", kind := "FIS"
    goal := some (.bin "≠" (.set [.num 0]) (.set [])) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty nondeterministicFixtureProject
  positiveFisObligation).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty nondeterministicFixtureProject
  { positiveFisObligation with goal := some (.bin "≠" (.set [.num 1]) (.set [])) }).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty nondeterministicFixtureProject
  { positiveFisObligation with component := "N" }).isSome

private def positiveFisPO :
    CheckedPO EventB.Theory.empty nondeterministicFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty nondeterministicFixtureProject
    positiveFisObligation).get (by native_decide)

private def positiveFisSource : CheckedRelationalEventSource EventB.Theory.empty
    nondeterministicFixtureProject positiveFisPO.obligation.component "INITIALISATION" := by
  have component : positiveFisPO.obligation.component = "M" := by native_decide
  rw [component]
  exact (CheckedRelationalEventSource.fromProject EventB.Theory.empty
    nondeterministicFixtureProject "M" "INITIALISATION").get (by native_decide)

#guard positiveFisSource.relations ==
  [.bin "∈" (.id "x'") (.set [.num 0])]

private def fisFixtureTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 0)] }
    after := { values := [("x", .integer 0)] }
    declarations := [("x", .int)] }

private theorem fisFixtureRelation :
    positiveFisSource.relationAction 128 fisFixtureTransition := by
  have declarations : positiveFisSource.declarations = [("x", .int)] := by
    native_decide
  have relations : positiveFisSource.relations =
      [.bin "∈" (.id "x'") (.set [.num 0])] := by
    native_decide
  unfold CheckedRelationalEventSource.relationAction
  constructor
  · simpa [declarations, fisFixtureTransition]
  constructor
  · native_decide
  constructor
  · native_decide
  · intro relation member
    simp only [relations, List.mem_singleton] at member
    subst relation
    exact assignmentPredicate_x_prime_in_zero

private abbrev fisSourceState :=
  { transition : CheckedBeforeAfter //
      positiveFisSource.relationAction 128 transition }

private def fisFixtureState : fisSourceState := ⟨fisFixtureTransition, fisFixtureRelation⟩

private def fisSourceModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := positiveFisSource.relationAction 128
    inhabited := ⟨fisFixtureTransition, fisFixtureRelation⟩
    supports := fun _ => true }

private def positiveFisAdapter : FisAdapter EventB.Theory.empty
    nondeterministicFixtureProject fisSourceState :=
  { binding := positiveFisPO
    eventLabel := "INITIALISATION"
    actionLabel := "choose"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveFisSource
    pre := fun _ => True
    action := fun _ _ => True
    fuel := 128
    formula :=
      { evaluator := fisSourceModel
        encode := fun state => state.1.1
        declarations := [("x", .int)]
        declarationScope := some "INITIALISATION"
        declarationsBound := by
          have component : positiveFisPO.obligation.component = "M" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty nondeterministicFixtureProject
            "M" "INITIALISATION" = some [("x", .int)]
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.2 with ⟨declared, _, _, _⟩
          have sourceDeclarations : positiveFisSource.declarations = [("x", .int)] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by
          intro state
          exact state.1.2
        sourceValid := by
          intro state
          exact state.1.2
        sourceComplete := by
          intro transition source
          exact ⟨(⟨transition, source⟩, fisFixtureState), rfl⟩
        evaluatorValid := by
          simpa only [show positiveFisPO.obligation = positiveFisObligation by native_decide] using
            (typedTransitionModel_closed_validOnDomain fisSourceModel
              (positiveFisSource.relationAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact ⟨by simpa [declared] using beforeValid,
                  by simpa [declared] using afterValid⟩)
              positiveFisObligation (by native_decide) (by native_decide)
              (.bin "≠" (.set [.num 0]) (.set [])) (by native_decide) (by native_decide)
              (by rfl) (by rfl)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                have beforeValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.before = true := by
                  simpa [declared] using beforeValid
                have afterValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.after = true := by
                  simpa [declared] using afterValid
                exact evalBeforeAfterZeroSetNeEmpty transition beforeValid' afterValid'))
        adequate := by
          intro _ before _
          exact ⟨before, trivial⟩ }
    fuelExact := by rfl
    actionExact := by
      intro state
      constructor
      · intro _
        exact state.1.2
      · intro _
        trivial
    nonempty := ⟨fisFixtureState, trivial⟩ }

example : feasibilitySemantic positiveFisAdapter.pre positiveFisAdapter.action :=
  positiveFisAdapter.sound

/- Minimal model-derived witness matrix.  The denominator is the literal one so
   WFIS remains executable while WWD still exercises the generated definedness
   obligation; the adapter's semantic witness bridge remains a later boundary. -/

private def witnessFixtureProject : EventB.Typing.Project :=
  [ { name := "A"
      elem := .machineFile [("org.eventb.core.name", "A")] [
        .variable [("org.eventb.core.identifier", "x")] [],
        .event [("org.eventb.core.label", "INITIALISATION")] [],
        .event [("org.eventb.core.label", "step")] [
          .parameter [("org.eventb.core.identifier", "p")] [],
          .guard [("org.eventb.core.label", "g"),
            ("org.eventb.core.predicate", "1 = 1")] [],
          .action [("org.eventb.core.label", "set"),
            ("org.eventb.core.assignment", "x ≔ p")] []
        ]
      ] }
  , { name := "B"
      elem := .machineFile [("org.eventb.core.name", "B")] [
        .refinesMachine [("org.eventb.core.target", "A")] [],
        .variable [("org.eventb.core.identifier", "x")] [],
        .event [("org.eventb.core.label", "INITIALISATION")] [],
        .event [("org.eventb.core.label", "step")] [
          .refinesEvent [("org.eventb.core.target", "step")] [],
          .parameter [("org.eventb.core.identifier", "q")] [],
          .guard [("org.eventb.core.label", "g"),
            ("org.eventb.core.predicate", "1 = 1")] [],
          .witness [("org.eventb.core.label", "p"),
            ("org.eventb.core.predicate", "p = 0 ÷ 1")] [],
          .action [("org.eventb.core.label", "set"),
            ("org.eventb.core.assignment", "x ≔ q")] []
        ]
      ] }
  ]

private def positiveWfisObligation : Obligation :=
  { component := "B", name := "step/p/WFIS", kind := "WFIS"
    hyps := [.bin "=" (.num 1) (.num 1)]
    goal := some (.bind "∃" (.bin "⦂" (.id "p") (.id "ℤ"))
      (.bin "=" (.id "p") (.bin "÷" (.num 0) (.num 1)))) }

private def positiveWwdObligation : Obligation :=
  { component := "B", name := "step/p/WWD", kind := "WWD"
    hyps := [.bin "=" (.num 1) (.num 1),
      .bin "≠" (.num 1) (.num 0)] }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
  positiveWfisObligation).isSome
#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
  positiveWwdObligation).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
  { positiveWfisObligation with
      goal := some (.bind "∃" (.bin "⦂" (.id "p") (.id "ℤ"))
        (.bin "=" (.id "p") (.num 1))) }).isSome
#guard !(CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
  { positiveWwdObligation with component := "A" }).isSome

private def positiveWfisPO :
    CheckedPO EventB.Theory.empty witnessFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
    positiveWfisObligation).get (by native_decide)

private def positiveWwdPO :
    CheckedPO EventB.Theory.empty witnessFixtureProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty witnessFixtureProject
    positiveWwdObligation).get (by native_decide)

private def positiveWitnessEventSource : CheckedEventSource EventB.Theory.empty
    witnessFixtureProject positiveWfisPO.obligation.component "step" := by
  have component : positiveWfisPO.obligation.component = "B" := by native_decide
  rw [component]
  exact (CheckedEventSource.fromProject EventB.Theory.empty witnessFixtureProject
    "B" "step").get (by native_decide)

#guard positiveWitnessEventSource.updates == [("x", .id "q")]
#guard (CheckedWitnessSource.fromProject EventB.Theory.empty witnessFixtureProject
  "B" "step" "p").isSome
#guard (CheckedWitnessSource.fromProject EventB.Theory.empty witnessFixtureProject
  "B" "step" "missing").isNone
#guard positiveWfisPO.obligation.name == "step/p/WFIS"
#guard positiveWwdPO.obligation.name == "step/p/WWD"

private def positiveWitnessSource : CheckedWitnessSource EventB.Theory.empty
    witnessFixtureProject "B" "step" "p" :=
  (CheckedWitnessSource.fromProject EventB.Theory.empty witnessFixtureProject
    "B" "step" "p").get (by native_decide)

private def witnessFormulaModel : TypedFormulaModel :=
  { declarations := [("x", .int), ("q", .int), ("p", .int)]
    fuel := 128
    wellFormed := fun env =>
      ValueEnv.validationOk 128 [("x", .int), ("q", .int), ("p", .int)] env = true
    inhabited := ⟨{ values := [("x", .integer 0), ("q", .integer 0), ("p", .integer 0)] },
      by native_decide⟩
    validated := fun _ proof => proof
    complete := fun _ proof => proof
    supports := supportsPredicate }

private abbrev witnessState :=
  { env : ValueEnv //
      ValueEnv.validationOk 128 [("x", .int), ("q", .int), ("p", .int)] env = true }

private theorem witnessFormulaModel_wfis_valid :
    TypedFormulaModel.validUnchecked witnessFormulaModel positiveWfisObligation := by
  constructor
  · native_decide
  constructor
  · rfl
  · intro env _
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        exact evalWitnessIntegerZeroDivOne env
      · intro hypothesis member
        simp only [positiveWfisObligation, List.mem_singleton] at member
        subst hypothesis
        refine ⟨true, ?_⟩
        exact evalPredicateIntegerOneEqOne env
    · intro _
      exact evalWitnessIntegerZeroDivOne env

private theorem witnessFormulaModel_wwd_valid :
    TypedFormulaModel.validUnchecked witnessFormulaModel positiveWwdObligation := by
  constructor
  · native_decide
  · intro env _ hypothesis member
    simp only [positiveWwdObligation] at member
    simp only [List.mem_cons, List.mem_singleton] at member
    rcases member with h | h
    · have h' : hypothesis = .bin "=" (.num 1) (.num 1) := by
        simpa using h
      subst hypothesis
      exact ⟨⟨true, evalPredicateIntegerOneEqOne env⟩,
        evalPredicateIntegerOneEqOne env⟩
    · have h' : hypothesis = .bin "≠" (.num 1) (.num 0) := by
        simpa using h
      subst hypothesis
      exact ⟨⟨true, evalPredicateIntegerOneNeZero env⟩,
        evalPredicateIntegerOneNeZero env⟩

private def positiveWwdSource : CheckedWitnessSource EventB.Theory.empty
    witnessFixtureProject "B" "step" "p" := positiveWitnessSource

private def positiveWfisAdapterSource : CheckedWitnessSource EventB.Theory.empty
    witnessFixtureProject positiveWfisPO.obligation.component "step" "p" := by
  have component : positiveWfisPO.obligation.component = "B" := by native_decide
  rw [component]
  exact positiveWitnessSource

private def positiveWwdAdapterSource : CheckedWitnessSource EventB.Theory.empty
    witnessFixtureProject positiveWwdPO.obligation.component "step" "p" := by
  have component : positiveWwdPO.obligation.component = "B" := by native_decide
  rw [component]
  exact positiveWitnessSource

private def positiveWfisAdapter : WfisAdapter EventB.Theory.empty
    witnessFixtureProject witnessState Int :=
  { binding := positiveWfisPO
    eventLabel := "step"
    witnessLabel := "p"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveWfisAdapterSource
    sourcePredicate := positiveWfisAdapterSource.predicate
    sourcePredicateExact := rfl
    pre := fun _ => True
    defined := fun _ => True
    predicate := fun _ witness => witness = (0 : Int)
    contract :=
      { feasible := by
          intro _ _
          exact ⟨0, rfl⟩
        wellDefined := by
          intro _ _
          trivial }
    formula :=
      { evaluator := witnessFormulaModel
        encode := fun state => state.1
        declarationScope := some "step"
        declarationsBound := by
          have component : positiveWfisPO.obligation.component = "B" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty witnessFixtureProject "B" "step" =
            some [("x", .int), ("q", .int), ("p", .int)]
          native_decide
        stateValid := by
          intro state
          exact state.2
        stateComplete := by
          intro env proof
          exact ⟨⟨env, proof⟩, rfl⟩
        evaluatorValid := by
          simpa only [show positiveWfisPO.obligation = positiveWfisObligation by native_decide]
            using witnessFormulaModel_wfis_valid
        adequate := by
          intro _ state _
          exact ⟨0, rfl⟩ }
    nonempty := by
      exact ⟨⟨{ values := [("x", .integer 0), ("q", .integer 0), ("p", .integer 0)] },
        by native_decide⟩,
        trivial⟩ }

private def positiveWwdAdapter : WwdAdapter EventB.Theory.empty
    witnessFixtureProject witnessState Int :=
  { binding := positiveWwdPO
    eventLabel := "step"
    witnessLabel := "p"
    kind := by native_decide
    sourceName := by native_decide
    eventSource := positiveWwdAdapterSource
    sourcePredicate := positiveWwdAdapterSource.predicate
    sourcePredicateExact := rfl
    pre := fun _ => True
    defined := fun _ => True
    predicate := fun _ witness => witness = (0 : Int)
    contract :=
      { feasible := by
          intro _ _
          exact ⟨0, rfl⟩
        wellDefined := by
          intro _ _
          trivial }
    formula :=
      { evaluator := witnessFormulaModel
        encode := fun state => state.1
        declarationScope := some "step"
        declarationsBound := by
          have component : positiveWwdPO.obligation.component = "B" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty witnessFixtureProject "B" "step" =
            some [("x", .int), ("q", .int), ("p", .int)]
          native_decide
        stateValid := by
          intro state
          exact state.2
        stateComplete := by
          intro env proof
          exact ⟨⟨env, proof⟩, rfl⟩
        evaluatorValid := by
          simpa only [show positiveWwdPO.obligation = positiveWwdObligation by native_decide] using
            witnessFormulaModel_wwd_valid
        adequate := by
          intro _ _ _
          trivial } }

example : witnessFeasibilitySemantic positiveWfisAdapter.pre positiveWfisAdapter.predicate :=
  positiveWfisAdapter.sound

example : witnessDefinednessSemantic positiveWwdAdapter.pre positiveWwdAdapter.defined :=
  positiveWwdAdapter.sound

private def constantVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .variant [("org.eventb.core.expression", "0")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                     ("org.eventb.core.assignment", "x ≔ 0")] [] ]
       , .event [("org.eventb.core.label", "step"),
                 ("org.eventb.core.convergence", "2")]
           [ .action [("org.eventb.core.label", "set"),
                     ("org.eventb.core.assignment", "x ≔ x")] [] ] ] }]

private def constantNatObligation : Obligation :=
  { component := "M", name := "step/NAT", kind := "NAT"
    goal := some (.bin "∈" (.num 0) (.id "ℕ")) }

private def constantVarObligation : Obligation :=
  { component := "M", name := "step/VAR", kind := "VAR"
    goal := some (.bin "≤" (.num 0) (.num 0)) }

#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantVariantProject
  constantNatObligation).isSome
#guard (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantVariantProject
  constantVarObligation).isSome
#guard (CheckedVariantSource.fromProject constantVariantProject "M").isSome

private def constantNatPO : CheckedPO EventB.Theory.empty constantVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantVariantProject
    constantNatObligation).get (by native_decide)

private def constantVarPO : CheckedPO EventB.Theory.empty constantVariantProject :=
  (CheckedPO.fromGeneratedExact? EventB.Theory.empty constantVariantProject
    constantVarObligation).get (by native_decide)

private def constantVariantEventSource : CheckedEventSource EventB.Theory.empty
    constantVariantProject "M" "step" :=
  (CheckedEventSource.fromProject EventB.Theory.empty constantVariantProject "M" "step").get
    (by native_decide)

private def constantVariantSource : CheckedVariantSource constantVariantProject "M" :=
  (CheckedVariantSource.fromProject constantVariantProject "M").get (by native_decide)

private def constantNatEventSource : CheckedEventSource EventB.Theory.empty
    constantVariantProject constantNatPO.obligation.component "step" := by
  have component : constantNatPO.obligation.component = "M" := by native_decide
  rw [component]
  exact constantVariantEventSource

private def constantNatVariantSource : CheckedVariantSource constantVariantProject
    constantNatPO.obligation.component := by
  have component : constantNatPO.obligation.component = "M" := by native_decide
  rw [component]
  exact constantVariantSource

private def constantVariantTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 0)] }
    after := { values := [("x", .integer 0)] }
    declarations := [("x", .int)] }

private theorem constantVariantAssignment :
    constantNatEventSource.assignmentAction 128 constantVariantTransition := by
  change assignmentRelation 128 constantNatEventSource.declarations
    constantVariantTransition constantNatEventSource.updates
  have declarations : constantNatEventSource.declarations = [("x", .int)] := by
    native_decide
  have updates : constantNatEventSource.updates = [("x", .id "x")] := by
    native_decide
  rw [declarations, updates]
  exact assignmentRelation_x_self_zero

private abbrev constantVariantState :=
  { transition : CheckedBeforeAfter //
      constantNatEventSource.assignmentAction 128 transition }

private def constantVariantStateValue : constantVariantState :=
  ⟨constantVariantTransition, constantVariantAssignment⟩

private def constantVariantModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := constantNatEventSource.assignmentAction 128
    inhabited := ⟨constantVariantTransition, constantVariantAssignment⟩
    supports := fun _ => true }

private def constantIntegerVariant : IntegerVariant constantVariantState :=
  { source := "step"
    mode := .anticipated
    measure := fun _ => 0
    action := fun before _ => constantNatEventSource.assignmentAction 128 before.1
    natural := by intro; omega
    progress := by
      intro before after _
      simp [integerVariantProgress] }

private def constantIntegerVariantAdapter :
    IntegerVariantAdapter EventB.Theory.empty constantVariantProject constantVariantState :=
  { natBinding := constantNatPO
    varBinding := constantVarPO
    natKind := by native_decide
    varKind := by native_decide
    componentMatch := by native_decide
    eventLabel := "step"
    eventSource := constantNatEventSource
    variantSource := constantNatVariantSource
    natName := by native_decide
    varName := by native_decide
    contract := constantIntegerVariant
    sourceMatch := by native_decide
    fuel := 128
    natFormula :=
      { evaluator := constantVariantModel
        encode := fun state => state.1.1
        declarations := [("x", .int)]
        declarationScope := some "step"
        declarationsBound := by
          have component : constantNatPO.obligation.component = "M" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty constantVariantProject "M" "step" =
            some [("x", .int)]
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.2 with ⟨declared, _, _, _⟩
          have sourceDeclarations : constantNatEventSource.declarations = [("x", .int)] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by intro state; exact state.1.2
        sourceValid := by intro state; exact state.1.2
        sourceComplete := by
          intro transition source
          exact ⟨(⟨transition, source⟩, constantVariantStateValue), rfl⟩
        evaluatorValid := by
          simpa only [show constantNatPO.obligation = constantNatObligation by native_decide] using
            (typedTransitionModel_closed_validOnDomain constantVariantModel
              (constantNatEventSource.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact ⟨by simpa [declared] using beforeValid,
                  by simpa [declared] using afterValid⟩)
              constantNatObligation (by native_decide) (by native_decide)
              (.bin "∈" (.num 0) (.id "ℕ")) (by native_decide) (by native_decide)
              (by rfl) (by rfl)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                have beforeValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.before = true := by
                  simpa [declared] using beforeValid
                have afterValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.after = true := by
                  simpa [declared] using afterValid
                exact evalBeforeAfterZeroNat transition beforeValid' afterValid'))
        adequate := by intro _; exact constantIntegerVariant.natural }
    varFormula :=
      { evaluator := constantVariantModel
        encode := fun state => state.1.1
        declarations := [("x", .int)]
        declarationScope := some "step"
        declarationsBound := by
          have component : constantVarPO.obligation.component = "M" := by native_decide
          simp only [component]
          change exactEventDeclarations? EventB.Theory.empty constantVariantProject "M" "step" =
            some [("x", .int)]
          native_decide
        transitionDeclarations := by
          intro state
          rcases state.1.2 with ⟨declared, _, _, _⟩
          have sourceDeclarations : constantNatEventSource.declarations = [("x", .int)] := by
            native_decide
          simpa [sourceDeclarations] using declared
        transitionValid := by intro state; exact state.1.2
        sourceValid := by intro state; exact state.1.2
        sourceComplete := by
          intro transition source
          exact ⟨(⟨transition, source⟩, constantVariantStateValue), rfl⟩
        evaluatorValid := by
          simpa only [show constantVarPO.obligation = constantVarObligation by native_decide] using
            (typedTransitionModel_closed_validOnDomain constantVariantModel
              (constantNatEventSource.assignmentAction 128)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                exact ⟨by simpa [declared] using beforeValid,
                  by simpa [declared] using afterValid⟩)
              constantVarObligation (by native_decide) (by native_decide)
              (.bin "≤" (.num 0) (.num 0)) (by native_decide) (by native_decide)
              (by rfl) (by rfl)
              (by
                intro transition source
                rcases source with ⟨declared, beforeValid, afterValid, _⟩
                have beforeValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.before = true := by
                  simpa [declared] using beforeValid
                have afterValid' :
                    ValueEnv.validationOk 128 transition.declarations transition.after = true := by
                  simpa [declared] using afterValid
                exact evalBeforeAfterZeroLeZero transition beforeValid' afterValid'))
        adequate := by intro _; exact constantIntegerVariant.progress }
    fuelExact := by constructor <;> rfl
    natActionExact := by intro state; exact Iff.rfl
    varActionExact := by intro state; exact Iff.rfl }

example : integerVariantNaturality constantIntegerVariantAdapter.contract ∧
    integerVariantProgressSemantic constantIntegerVariantAdapter.contract :=
  constantIntegerVariantAdapter.sound

/- A disjoint acceptance matrix.  These rows deliberately do not reuse the larger
   variant/event fixtures below: each mutation changes one provenance field while
   still going through the checked generator and source binders. -/
private def theoremMatrixGoal : EventB.Formula.Term :=
  .bin "=" (.num 1) (.num 1)

private def theoremMatrixChecked? (goal : EventB.Formula.Term) :
    Option (CheckedPO EventB.Theory.empty theoremFixtureProject) :=
  CheckedPO.fromGenerated? EventB.Theory.empty theoremFixtureProject "M"
    (fun obligation => obligation.component == "M" &&
      obligation.kind == "THM" && obligation.name == "taut/THM" &&
      obligation.goal == some goal)

#guard (theoremMatrixChecked? theoremMatrixGoal).isSome
#guard !(theoremMatrixChecked? (.bin "=" (.num 1) (.num 2))).isSome
#guard !(CheckedPO.fromGenerated? EventB.Theory.empty theoremFixtureProject "M"
  (fun obligation => obligation.component == "N" &&
    obligation.kind == "THM" && obligation.name == "taut/THM" &&
    obligation.goal == some theoremMatrixGoal)).isSome

private def sourceMatrixProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "x ∈ ℤ")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 0")] [] ]
       , .event [("org.eventb.core.label", "step")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ x")] [] ]
       , .event [("org.eventb.core.label", "other")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 1")] [] ] ] }
   , { name := "N"
       elem := .machineFile [("org.eventb.core.name", "N")]
         [ .variable [("org.eventb.core.identifier", "x")] []
         , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
         , .event [("org.eventb.core.label", "INITIALISATION")]
             [ .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ 0")] [] ]
         , .event [("org.eventb.core.label", "step")]
             [ .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ 2")] [] ] ] }]

private def sourceMatrixUpdates? (component event : String) :
    Option (List (String × EventB.Formula.Term)) :=
  (CheckedEventSource.fromProject EventB.Theory.empty sourceMatrixProject component event).map
    (·.updates)

#guard sourceMatrixUpdates? "M" "step" == some [("x", .id "x")]
#guard sourceMatrixUpdates? "M" "other" == some [("x", .num 1)]
#guard !(sourceMatrixUpdates? "M" "step" == some [("x", .num 1)])
#guard (sourceMatrixUpdates? "M" "missing").isNone
#guard !(sourceMatrixUpdates? "M" "step" == sourceMatrixUpdates? "N" "step")

private def variantMatrixProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .variant [("org.eventb.core.expression", "x")] [] ] }
   , { name := "N"
       elem := .machineFile [("org.eventb.core.name", "N")]
         [ .variable [("org.eventb.core.identifier", "y")] []
         , .variant [("org.eventb.core.expression", "y")] [] ] }]

private def variantMatrixExpression? (component : String) : Option EventB.Formula.Term :=
  (CheckedVariantSource.fromProject variantMatrixProject component).map (·.expression)

#guard variantMatrixExpression? "M" == some (.id "x")
#guard variantMatrixExpression? "N" == some (.id "y")
#guard !(variantMatrixExpression? "M" == some (.id "y"))
#guard !(variantMatrixExpression? "M" == variantMatrixExpression? "N")
#guard (variantMatrixExpression? "missing").isNone

#guard !(Obligation.sourceBound variantMatrixProject
  { component := "M", name := "N/VAR", kind := "VAR" })
#guard !(Obligation.sourceBound sourceMatrixProject
  { component := "M", name := "missing/VAR", kind := "VAR" })

#guard match generateCheckedIn EventB.Theory.empty finiteVariantProject "M" with
  | .ok obligations =>
      match obligations.find? (fun obligation => obligation.kind == "NAT"),
        obligations.find? (fun obligation => obligation.kind == "VAR") with
      | some nat, some var => finiteVariantSourceMatch "step" nat var
      | _, _ => false
  | .error _ => false

private def finiteSetVariantProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [ .variable [("org.eventb.core.identifier", "S")] []
       , .invariant [("org.eventb.core.label", "type"),
                    ("org.eventb.core.predicate", "S ∈ ℙ(ℤ)")] []
       , .variant [("org.eventb.core.expression", "S")] []
       , .event [("org.eventb.core.label", "INITIALISATION")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "S ≔ ∅")] [] ]
       , .event [("org.eventb.core.label", "step"),
                 ("org.eventb.core.convergence", "1")]
           [ .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "S ≔ S")] [] ] ] }]

#guard match CheckedVariantSource.fromProject finiteSetVariantProject "M" with
  | some source => EventB.Formula.print source.expression == "S"
  | none => false

#guard (CheckedPO.fromGenerated? EventB.Theory.empty finiteSetVariantProject "M"
  (fun obligation => obligation.kind == "FIN" && obligation.name == "FIN")).isSome

#guard (CheckedPO.fromGenerated? EventB.Theory.empty finiteSetVariantProject "M"
  (fun obligation => obligation.kind == "VAR" && obligation.name == "step/VAR")).isSome

#guard !(CheckedPO.fromGenerated? EventB.Theory.empty finiteSetVariantProject "M"
  (fun obligation => obligation.kind == "FIN" && obligation.name == "step/FIN")).isSome

#guard !(CheckedPO.fromGenerated? EventB.Theory.empty finiteSetVariantProject "M"
  (fun obligation => obligation.kind == "VAR" && obligation.name == "other/VAR")).isSome

#guard match
    CheckedEventSource.fromProject EventB.Theory.empty finiteSetVariantProject "M" "step" with
  | some source => source.updates == [("S", .id "S")]
  | none => false

#guard match
    CheckedEventSource.fromProject EventB.Theory.empty finiteSetVariantProject "M" "missing" with
  | none => true
  | some _ => false

#guard match generateCheckedIn EventB.Theory.empty finiteSetVariantProject "M" with
  | .ok obligations =>
      match obligations.find? (fun (obligation : Obligation) => obligation.kind == "FIN"),
        obligations.find? (fun (obligation : Obligation) => obligation.kind == "VAR") with
      | some fin, some var => finiteSetVariantSourceMatch "step" fin var &&
          Obligation.sourceBound finiteSetVariantProject fin
      | _, _ => false
  | .error _ => false

#guard !finiteSetVariantSourceMatch "step"
  { name := "other/FIN", kind := "FIN" }
  { name := "step/VAR", kind := "VAR" }

end EventB.POG
