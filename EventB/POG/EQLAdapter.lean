/-
The first executable source adapter is deliberately small: integer EQL only.
Sets and parameterised events need additional canonicalisation and event identity
proofs, so they remain outside the accepting surface.
-/

import EventB.POGSoundness
import EventB.Semantics

namespace EventB.POG

universe u

def eqlGoal (name : String) : EventB.Formula.Term :=
  .bin "=" (.id (name ++ "'")) (.id name)

def intRead (name : String) (env : ValueEnv) : Option Int :=
  match env.lookup name with
  | some (.integer value) => some value
  | _ => none

def exactEqlShape (origin : EqlOrigin) (obligation : Obligation) : Bool :=
  obligation.component == origin.component && obligation.kind == "EQL" &&
    obligation.name == origin.event ++ "/" ++ origin.eqlVariable ++ "/EQL" &&
    obligation.goal == some (eqlGoal origin.eqlVariable)

structure EqlIntBinding (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) where
  component : String
  eventLabel : String
  eqlVariable : String
  origin : EqlOrigin
  obligation : Obligation
  located :
    locateEql? theory project component eventLabel eqlVariable =
      .ok (some (origin, obligation))
  sourceShape : exactEqlShape origin obligation = true
  valuation : ComponentValuation
  valuationChecked :
    ComponentValuation.fromProject theory project component = .ok valuation
  declarations : List (String × EventB.Typing.Ty)
  declarationsExact :
    declarations = valuation.declarationsForEvent project eventLabel
  updates : List (String × EventB.Formula.Term)
  exactUpdates :
    valuation.eventAssignments project eventLabel = .ok updates
  variableType :
    ValueEnv.declaredType? declarations eqlVariable = some .int

def EqlIntBinding.fromProject? (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component event eqlVariable : String) :
    Option (EqlIntBinding theory project) :=
  match located : locateEql? theory project component event eqlVariable with
  | .error _ | .ok none => none
  | .ok (some (origin, obligation)) =>
      if sourceShape : exactEqlShape origin obligation = true then
        match valuationChecked : ComponentValuation.fromProject theory project component with
        | .error _ => none
        | .ok valuation =>
            match exactUpdates : valuation.eventAssignments project event with
            | .error _ => none
            | .ok updates =>
                if variableType : ValueEnv.declaredType?
                    (valuation.declarationsForEvent project event) eqlVariable = some .int then
                  some
                    { origin
                      component
                      eventLabel := event
                      eqlVariable
                      obligation
                      located
                      sourceShape
                      valuation
                      valuationChecked
                      declarations := valuation.declarationsForEvent project event
                      declarationsExact := rfl
                      updates
                      exactUpdates
                      variableType }
                else none
      else none

def EqlIntBinding.action {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : EqlIntBinding theory project) (fuel : Nat)
    (before after : ValueEnv) : Prop :=
  ∃ transition : CheckedBeforeAfter,
    ValueEnv.parallelAssignTypedFuel fuel binding.declarations before binding.updates =
        .ok transition ∧ transition.after = after

def EqlIntBinding.goal {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : EqlIntBinding theory project) :
    EventB.Formula.Term := eqlGoal binding.eqlVariable

structure EqlIntEventBridge {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} (binding : EqlIntBinding theory project)
    (σ : Type u) where
  fuel : Nat
  encode : σ → ValueEnv
  event : Event σ
  declarationsExact :
    binding.declarations =
      binding.valuation.declarationsForEvent project binding.eventLabel
  stateValid : ∀ state,
    ValueEnv.validationOk fuel binding.declarations (encode state) = true
  actionExact : ∀ before after,
    event.act before after ↔ binding.action fuel (encode before) (encode after)
  unprimed : binding.eqlVariable.endsWith "'" = false
  primedBase :
    ((binding.eqlVariable ++ "'").dropEnd 1).copy = binding.eqlVariable
  primeNotInteger : binding.eqlVariable ++ "'" ≠ "ℤ"
  primeNotNatural : binding.eqlVariable ++ "'" ≠ "ℕ"
  primeNotNatural1 : binding.eqlVariable ++ "'" ≠ "ℕ1"
  primeNotBoolean : binding.eqlVariable ++ "'" ≠ "BOOL"
  notInteger : binding.eqlVariable ≠ "ℤ"
  notNatural : binding.eqlVariable ≠ "ℕ"
  notNatural1 : binding.eqlVariable ≠ "ℕ1"
  notBoolean : binding.eqlVariable ≠ "BOOL"
  hypothesesHold : ∀ {before after}, event.act before after →
    ∃ transition : CheckedBeforeAfter,
      transition.before = encode before ∧ transition.after = encode after ∧
      transition.declarations = binding.declarations ∧
      ValueEnv.validationOk fuel binding.declarations transition.before = true ∧
      ValueEnv.validationOk fuel binding.declarations transition.after = true ∧
      ∀ hypothesis ∈ binding.obligation.hyps,
        assignmentPredicateWithFuel fuel transition hypothesis
  stateInteger : ∀ state, ∃ value : Int,
    (encode state).lookup binding.eqlVariable = some (.integer value)
  nonempty : ∃ before after, event.act before after

def EqlIntEventBridge.read {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project}
    {binding : EqlIntBinding theory project} {σ : Type u}
    (bridge : EqlIntEventBridge binding σ) : σ → Option Int :=
  fun state => intRead binding.eqlVariable (bridge.encode state)

/- A kernel-checkable evaluator lemma. The lookup facts make the result independent
   of list order or the representation of unrelated variables. -/
theorem intRead_of_eqlEvaluation
    (fuel : Nat)
    (name : String) (transition : CheckedBeforeAfter)
    (beforeValue afterValue : Int)
    (beforeValid : ValueEnv.validationOk fuel transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk fuel transition.declarations transition.after = true)
    (unprimed : name.endsWith "'" = false)
    (primedBase : ((name ++ "'").dropEnd 1).copy = name)
    (primeNotInteger : name ++ "'" ≠ "ℤ")
    (primeNotNatural : name ++ "'" ≠ "ℕ")
    (primeNotNatural1 : name ++ "'" ≠ "ℕ1")
    (primeNotBoolean : name ++ "'" ≠ "BOOL")
    (notInteger : name ≠ "ℤ")
    (notNatural : name ≠ "ℕ")
    (notNatural1 : name ≠ "ℕ1")
    (notBoolean : name ≠ "BOOL")
    (beforeLookup : transition.before.lookup name = some (.integer beforeValue))
    (afterLookup : transition.after.lookup ((name ++ "'").dropEnd 1).copy =
      some (.integer afterValue))
    (evaluated : assignmentPredicateWithFuel fuel transition (eqlGoal name)) :
    afterValue = beforeValue := by
  exact eqlIntegerAfterEqBefore fuel name transition beforeValue afterValue
    beforeValid afterValid unprimed primedBase primeNotInteger primeNotNatural
    primeNotNatural1 primeNotBoolean notInteger notNatural notNatural1 notBoolean
    beforeLookup afterLookup evaluated

def EqlIntEventBridge.sequent {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project}
    {binding : EqlIntBinding theory project} {σ : Type u}
    (bridge : EqlIntEventBridge binding σ) : Prop :=
  ∀ transition : CheckedBeforeAfter,
    transition.declarations = binding.declarations →
    (∀ hypothesis ∈ binding.obligation.hyps,
      assignmentPredicateWithFuel bridge.fuel transition hypothesis) →
    assignmentPredicateWithFuel bridge.fuel transition (binding.goal)

theorem EqlIntEventBridge.sequent_of_goal_hypothesis
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {binding : EqlIntBinding theory project} {σ : Type u}
    (bridge : EqlIntEventBridge binding σ)
    (goalHypothesis : binding.goal ∈ binding.obligation.hyps) :
    bridge.sequent := by
  intro transition _ hypotheses
  exact hypotheses binding.goal goalHypothesis

theorem EqlIntEventBridge.framePreserved
    {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {binding : EqlIntBinding theory project} {σ : Type u}
    (bridge : EqlIntEventBridge binding σ)
    (poProof : bridge.sequent) :
    framePreserved bridge.read bridge.event.act := by
  intro before after eventStep
  obtain ⟨transition, beforeEq, afterEq, declarationsEq, beforeValid, afterValid,
    hypotheses⟩ := bridge.hypothesesHold eventStep
  have goal := poProof transition declarationsEq hypotheses
  obtain ⟨beforeValue, beforeLookup⟩ := bridge.stateInteger before
  obtain ⟨afterValue, afterLookup⟩ := bridge.stateInteger after
  have beforeValid' :
      ValueEnv.validationOk bridge.fuel transition.declarations transition.before = true := by
    simpa [declarationsEq] using beforeValid
  have afterValid' :
      ValueEnv.validationOk bridge.fuel transition.declarations transition.after = true := by
    simpa [declarationsEq] using afterValid
  have equal := intRead_of_eqlEvaluation bridge.fuel
    binding.eqlVariable transition beforeValue afterValue
    beforeValid' afterValid' bridge.unprimed bridge.primedBase
    bridge.primeNotInteger bridge.primeNotNatural bridge.primeNotNatural1 bridge.primeNotBoolean
    bridge.notInteger bridge.notNatural bridge.notNatural1 bridge.notBoolean
    (by simpa [beforeEq] using beforeLookup)
    (by simpa [afterEq, bridge.primedBase] using afterLookup) goal
  simp [EqlIntEventBridge.read, intRead,
    beforeLookup, afterLookup, equal]

/- A complete EQL acceptance object binds the generated obligation, the exact
   integer source, the executable event, and the proof of the checked sequent.
   The semantic theorem is then obtained only through the bridge above. -/
structure EqlIntAdapter (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (σ : Type u) where
  binding : EqlIntBinding theory project
  bridge : EqlIntEventBridge binding σ
  sequent : bridge.sequent

theorem EqlIntAdapter.sound {theory : EventB.Theory.Env}
    {project : EventB.Typing.Project} {σ : Type u}
    (adapter : EqlIntAdapter theory project σ) :
    framePreserved adapter.bridge.read adapter.bridge.event.act :=
  adapter.bridge.framePreserved adapter.sequent

/- ------------------------------------------------------------------ -/
/- Kernel fixtures.  The parent event has no action; the concrete event's
   deterministic self-assignment is therefore the exact source of B/step/x/EQL. -/

def positiveProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "x ≔ 0")] []]
        , .event [("org.eventb.core.label", "step")] []] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .invariant [("org.eventb.core.label", "type"),
                        ("org.eventb.core.predicate", "x ∈ ℤ")] []
          , .event [("org.eventb.core.label", "INITIALISATION")]
            [.action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ 0")] []]
          , .event [("org.eventb.core.label", "step")]
            [.refinesEvent [("org.eventb.core.target", "step")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ x")] []]] }]

#guard match locateEql? Theory.empty positiveProject "B" "step" "x" with
  | .ok (some (origin, obligation)) =>
      origin.component == "B" && origin.event == "step" &&
      origin.eqlVariable == "x" && obligation.kind == "EQL" &&
      obligation.name == "step/x/EQL" && obligation.goal == some (eqlGoal "x")
  | _ => false

#guard match ComponentValuation.fromProject Theory.empty positiveProject "B" with
  | .ok valuation =>
      match valuation.eventAssignments positiveProject "step" with
      | .ok [("x", .id "x")] => true
      | _ => false
  | .error _ => false

#guard match ComponentValuation.fromProject Theory.empty positiveProject "B" with
  | .ok valuation =>
      match valuation.eventAssignments positiveProject "step" with
      | .ok updates =>
          match valuation.parallelAssign positiveProject "step"
              { values := [("x", .integer 0)] } updates with
          | .ok transition =>
              ValueEnv.declaredType? transition.declarations "x" == some .int &&
                match evalBeforeAfter 128 transition (eqlGoal "x") with
                | .ok true => true
                | _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

#guard match locateEql? Theory.empty positiveProject "B" "step" "y" with
  | .ok none => true
  | _ => false

#guard match ComponentValuation.fromProject Theory.empty positiveProject "B" with
  | .ok valuation =>
      match valuation.parallelAssign positiveProject "step"
          { values := [("x", .integer 0)] } [("x", .num 1)] with
      | .error (.invalidTarget _) => true
      | _ => false
  | .error _ => false

example {theory : EventB.Theory.Env} {project : EventB.Typing.Project}
    {binding : EqlIntBinding theory project} {σ : Type u}
    (bridge : EqlIntEventBridge binding σ) (poProof : bridge.sequent) :
    framePreserved bridge.read bridge.event.act := by
  exact bridge.framePreserved poProof

end EventB.POG
