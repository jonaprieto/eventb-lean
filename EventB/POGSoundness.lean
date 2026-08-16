/-
Explicit semantic boundary for generated proof obligations.

The POG translates and names terms; this module lets a caller provide a model for
those terms and prove the resulting sequent. It does not guess the meaning of an
untyped formula, assignment, theory operator, or primed identifier.
-/

import EventB.POG
import EventB.Semantics

namespace EventB.POG

universe u

structure FormulaModel (σ : Type u) where
  denote : EventB.Formula.Term → σ → Prop

def validSequent {σ : Type u} (hyps : List (σ → Prop)) (goal : σ → Prop) : Prop :=
  ∀ state, (∀ hypothesis ∈ hyps, hypothesis state) → goal state

def validHypotheses {σ : Type u} (hyps : List (σ → Prop)) : Prop :=
  ∀ state, ∀ hypothesis ∈ hyps, hypothesis state

/- This is deliberately named unchecked: a formula-shaped record is not a generated
   Rodin obligation. The accepting entry point below requires exact membership in the
   strict generator output. -/
def FormulaModel.validUnchecked {σ : Type u} (model : FormulaModel σ)
    (obligation : Obligation) : Prop :=
  match obligation.kind, obligation.goal with
  | _, some goal => validSequent (obligation.hyps.map model.denote) (model.denote goal)
  | "WWD", none => validHypotheses (obligation.hyps.map model.denote)
  | _, none => False

theorem validSequent.intro {σ : Type u} {hyps : List (σ → Prop)} {goal : σ → Prop}
    (proof : ∀ state, (∀ hypothesis ∈ hyps, hypothesis state) → goal state) :
    validSequent hyps goal := proof

def Obligation.sourceBound (project : EventB.Typing.Project)
    (obligation : Obligation) : Bool :=
  EventB.POG.generatedSourceBound project obligation

def Obligation.checkedIn (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (obligation : Obligation) : Prop :=
  match generateCheckedIn theory project obligation.component with
  | .ok generated => obligation ∈ generated ∧ obligation.sourceBound project = true
  | .error _ => False

/- A caller-defined `denote` function is useful for local algebraic fixtures, but it
   is not a project semantics. Keep the name fail-closed until a source-bound
   adequacy theorem ties it to the typed evaluator and the Rodin translation. -/
def FormulaModel.valid {σ : Type u} (_model : FormulaModel σ)
    (_theory : EventB.Theory.Env) (_project : EventB.Typing.Project)
    (_obligation : Obligation) : Prop :=
  False

theorem FormulaModel.valid_of {σ : Type u} (model : FormulaModel σ)
    (obligation : Obligation)
    (proof : validSequent (obligation.hyps.map model.denote)
      (obligation.goal.map model.denote |>.getD fun _ => False)) :
    obligation.goal.isSome → model.validUnchecked obligation := by
  intro hasGoal
  cases goal : obligation.goal with
  | none => simp [goal] at hasGoal
  | some target =>
      simpa [FormulaModel.validUnchecked, goal] using proof

/- The generated POG surface is intentionally closed here. A new Rodin class must be
   added to this table before a typed semantic adapter can accept it. -/
inductive POClass where
  | inv | wd | grd | sim | thm | fis | wfis | wwd
  | eql | mrg | vwd | nat | fin | var
  deriving BEq, Repr

def POClass.ofKind : String → Option POClass
  | "INV" => some .inv
  | "WD" => some .wd
  | "GRD" => some .grd
  | "SIM" => some .sim
  | "THM" => some .thm
  | "FIS" => some .fis
  | "WFIS" => some .wfis
  | "WWD" => some .wwd
  | "EQL" => some .eql
  | "MRG" => some .mrg
  | "VWD" => some .vwd
  | "NAT" => some .nat
  | "FIN" => some .fin
  | "VAR" => some .var
  | _ => none

def POClass.valuationSupported : POClass → Bool
  | .thm | .wd | .vwd | .wfis | .wwd | .fin => true
  | _ => false

def POClass.transitionValuationSupported : POClass → Bool
  | .inv | .grd | .sim | .fis | .mrg | .eql | .nat | .var => true
  | _ => false

def Obligation.semanticShapeValid (obligation : Obligation) : Bool :=
  (POClass.ofKind obligation.kind).isSome && obligation.shapeValid &&
    !obligation.component.isEmpty && !obligation.name.isEmpty && obligation.diagnostics.isEmpty

def Obligation.valuationSupported (obligation : Obligation) : Bool :=
  match POClass.ofKind obligation.kind with
  | some poClass => poClass.valuationSupported
  | none => false

def Obligation.transitionValuationSupported (obligation : Obligation) : Bool :=
  match POClass.ofKind obligation.kind with
  | some poClass => poClass.transitionValuationSupported
  | none => false

#guard (POClass.ofKind "INV").isSome
#guard (POClass.ofKind "MRG").isSome
#guard (POClass.ofKind "VAR").isSome
#guard (POClass.ofKind "unknown").isNone
#guard !({ name := "bad/unknown", kind := "unknown", goal := some (.id "⊤") }
  : Obligation).semanticShapeValid
#guard !Obligation.valuationSupported
  ({ component := "M", name := "pending/INV", kind := "INV", goal := some (.id "⊤") } : Obligation)
#guard !(Obligation.semanticShapeValid
  ({ component := "M", name := "diagnostic/THM", kind := "THM",
     diagnostics := ["unresolved"], goal := some (.id "⊤") } : Obligation))

/- ------------------------------------------------------------------ -/
/- A small, executable semantic domain. Unsupported or ill-typed Event-B syntax returns
   an explicit error; callers must prove both evaluator coverage and definedness before
   using a formula as a valid sequent. -/

inductive ValueType where
  | integer
  | boolean
  | given (name : String)
  | finiteSet (element : Option ValueType)
  | pair (left right : ValueType)
  deriving Repr

private def valueTypeBeq : ValueType → ValueType → Bool
  | .integer, .integer | .boolean, .boolean => true
  | .given left, .given right => left == right
  | .finiteSet none, .finiteSet none => true
  | .finiteSet (some left), .finiteSet (some right) => valueTypeBeq left right
  | .pair left₁ right₁, .pair left₂ right₂ =>
      valueTypeBeq left₁ left₂ && valueTypeBeq right₁ right₂
  | _, _ => false

instance : BEq ValueType := ⟨valueTypeBeq⟩

private def valueTypeDecEq : (left right : ValueType) → Decidable (left = right)
  | .integer, .integer => isTrue rfl
  | .boolean, .boolean => isTrue rfl
  | .given left, .given right =>
      if equal : left = right then isTrue (by cases equal; rfl)
      else isFalse (by intro proof; cases proof; exact equal rfl)
  | .finiteSet left, .finiteSet right =>
      match left, right with
      | none, none => isTrue rfl
      | none, some _ => isFalse (by intro proof; cases proof)
      | some _, none => isFalse (by intro proof; cases proof)
      | some left, some right =>
          match valueTypeDecEq left right with
          | isTrue equal => isTrue (by cases equal; rfl)
          | isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .pair left₁ right₁, .pair left₂ right₂ =>
      match valueTypeDecEq left₁ left₂, valueTypeDecEq right₁ right₂ with
      | isTrue equal₁, isTrue equal₂ => isTrue (by cases equal₁; cases equal₂; rfl)
      | isFalse unequal, _ => isFalse (by intro proof; cases proof; exact unequal rfl)
      | _, isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .integer, .boolean | .integer, .given _ | .integer, .finiteSet _ | .integer, .pair _ _ |
    .boolean, .integer | .boolean, .given _ | .boolean, .finiteSet _ | .boolean, .pair _ _ |
    .given _, .integer | .given _, .boolean | .given _, .finiteSet _ | .given _, .pair _ _ |
    .finiteSet _, .integer | .finiteSet _, .boolean | .finiteSet _, .given _ |
    .finiteSet _, .pair _ _ | .pair _ _, .integer | .pair _ _, .boolean |
    .pair _ _, .given _ | .pair _ _, .finiteSet _ => isFalse (by intro proof; cases proof)

instance : DecidableEq ValueType := valueTypeDecEq

inductive EvalError where
  | fuelExhausted
  | unsupported (term : EventB.Formula.Term)
  | unbound (name : String)
  | typeMismatch (expected actual : ValueType)
  | divisionByZero
  | duplicateAssignment (name : String)
  | invalidTarget (name : String)
  | assignmentArity
  | partialApplication
  | invalidRelation
  | invalidValue
  deriving Repr, DecidableEq

inductive Value where
  | integer (value : Int)
  | boolean (value : Bool)
  | atom (carrier name : String)
  | set (values : List Value)
  | pair (left right : Value)
  /-- A typed powerset carrier, such as `ℙ(ℤ)`. -/
  | powerSet (element : ValueType)
  | integerSet
  | naturalSet
  | natural1Set
  | booleanSet
  deriving Repr, Inhabited

mutual

private def valueDecEq : (left right : Value) → Decidable (left = right)
  | .integer left, .integer right =>
      if equal : left = right then isTrue (by cases equal; rfl)
      else isFalse (by intro proof; cases proof; exact equal rfl)
  | .boolean left, .boolean right =>
      if equal : left = right then isTrue (by cases equal; rfl)
      else isFalse (by intro proof; cases proof; exact equal rfl)
  | .atom leftCarrier leftName, .atom rightCarrier rightName =>
      match decEq leftCarrier rightCarrier, decEq leftName rightName with
      | isTrue carrierEqual, isTrue nameEqual =>
          isTrue (by cases carrierEqual; cases nameEqual; rfl)
      | isFalse unequal, _ => isFalse (by intro proof; cases proof; exact unequal rfl)
      | _, isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .set left, .set right =>
      match valueListDecEq left right with
      | isTrue equal => isTrue (by cases equal; rfl)
      | isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .pair left₁ right₁, .pair left₂ right₂ =>
      match valueDecEq left₁ left₂, valueDecEq right₁ right₂ with
      | isTrue equal₁, isTrue equal₂ => isTrue (by cases equal₁; cases equal₂; rfl)
      | isFalse unequal, _ => isFalse (by intro proof; cases proof; exact unequal rfl)
      | _, isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .powerSet left, .powerSet right =>
      if equal : left = right then isTrue (by cases equal; rfl)
      else isFalse (by intro proof; cases proof; exact equal rfl)
  | .integerSet, .integerSet | .naturalSet, .naturalSet |
    .natural1Set, .natural1Set | .booleanSet, .booleanSet => isTrue rfl
  | .integer _, .boolean _ | .integer _, .atom _ _ | .integer _, .set _ | .integer _, .pair _ _ |
    .integer _, .powerSet _ | .integer _, .integerSet | .integer _, .naturalSet |
    .integer _, .natural1Set | .integer _, .booleanSet |
    .boolean _, .integer _ | .boolean _, .atom _ _ | .boolean _, .set _ | .boolean _, .pair _ _ |
    .boolean _, .powerSet _ | .boolean _, .integerSet | .boolean _, .naturalSet |
    .boolean _, .natural1Set | .boolean _, .booleanSet |
    .atom _ _, .integer _ | .atom _ _, .boolean _ | .atom _ _, .set _ | .atom _ _, .pair _ _ |
    .atom _ _, .powerSet _ | .atom _ _, .integerSet | .atom _ _, .naturalSet |
    .atom _ _, .natural1Set | .atom _ _, .booleanSet |
    .set _, .integer _ | .set _, .boolean _ | .set _, .atom _ _ | .set _, .pair _ _ |
    .set _, .powerSet _ | .set _, .integerSet | .set _, .naturalSet |
    .set _, .natural1Set | .set _, .booleanSet |
    .pair _ _, .integer _ | .pair _ _, .boolean _ | .pair _ _, .atom _ _ | .pair _ _, .set _ |
    .pair _ _, .powerSet _ | .pair _ _, .integerSet | .pair _ _, .naturalSet |
    .pair _ _, .natural1Set | .pair _ _, .booleanSet |
    .powerSet _, .integer _ | .powerSet _, .boolean _ | .powerSet _, .atom _ _ |
    .powerSet _, .set _ | .powerSet _, .pair _ _ | .powerSet _, .integerSet |
    .powerSet _, .naturalSet | .powerSet _, .natural1Set | .powerSet _, .booleanSet |
    .integerSet, .integer _ | .integerSet, .boolean _ | .integerSet, .atom _ _ |
    .integerSet, .set _ | .integerSet, .pair _ _ | .integerSet, .powerSet _ |
    .integerSet, .naturalSet | .integerSet, .natural1Set | .integerSet, .booleanSet |
    .naturalSet, .integer _ | .naturalSet, .boolean _ | .naturalSet, .atom _ _ |
    .naturalSet, .set _ | .naturalSet, .pair _ _ | .naturalSet, .powerSet _ |
    .naturalSet, .integerSet | .naturalSet, .natural1Set | .naturalSet, .booleanSet |
    .natural1Set, .integer _ | .natural1Set, .boolean _ | .natural1Set, .atom _ _ |
    .natural1Set, .set _ | .natural1Set, .pair _ _ | .natural1Set, .powerSet _ |
    .natural1Set, .integerSet | .natural1Set, .naturalSet | .natural1Set, .booleanSet |
    .booleanSet, .integer _ | .booleanSet, .boolean _ | .booleanSet, .atom _ _ |
    .booleanSet, .set _ | .booleanSet, .pair _ _ | .booleanSet, .powerSet _ |
    .booleanSet, .integerSet | .booleanSet, .naturalSet | .booleanSet, .natural1Set =>
      isFalse (by intro proof; cases proof)

private def valueListDecEq : (left right : List Value) → Decidable (left = right)
  | [], [] => isTrue rfl
  | left :: lefts, right :: rights =>
      match valueDecEq left right, valueListDecEq lefts rights with
      | isTrue equal₁, isTrue equal₂ => isTrue (by cases equal₁; cases equal₂; rfl)
      | isFalse unequal, _ => isFalse (by intro proof; cases proof; exact unequal rfl)
      | _, isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro proof; cases proof)

end

instance : DecidableEq Value := valueDecEq

def Value.typeOf : Value → ValueType
  | .integer _ => .integer
  | .boolean _ => .boolean
  | .atom carrier _ => .given carrier
  | .set (value :: _) => .finiteSet (some value.typeOf)
  | .set [] => .finiteSet none
  | .pair left right => .pair left.typeOf right.typeOf
  | .powerSet element => .finiteSet (some (.finiteSet (some element)))
  | .integerSet | .naturalSet | .natural1Set => .finiteSet (some .integer)
  | .booleanSet => .finiteSet (some .boolean)

def Value.setType : List Value → ValueType
  | [] => .finiteSet none
  | first :: _ => .finiteSet (some first.typeOf)

def ValueType.compatible : ValueType → ValueType → Bool
  | .given left, .given right => left == right
  | .finiteSet left, .finiteSet right =>
      match left, right with
      | some left, some right => compatible left right
      | _, _ => true
  | .pair left₁ right₁, .pair left₂ right₂ =>
      compatible left₁ left₂ && compatible right₁ right₂
  | left, right => left == right

def Value.sameType (left right : Value) : Bool :=
  ValueType.compatible left.typeOf right.typeOf

private def Value.isWellFormed : Nat → Value → Bool
  | 0, _ => false
  | fuel + 1, .integer _ | fuel + 1, .boolean _ | fuel + 1, .atom _ _ | fuel + 1, .integerSet |
      fuel + 1, .naturalSet | fuel + 1, .natural1Set | fuel + 1, .booleanSet => true
  | fuel + 1, .pair left right =>
      Value.isWellFormed fuel left && Value.isWellFormed fuel right
  | fuel + 1, .set values =>
      values.all (Value.isWellFormed fuel) && match values with
        | [] => true
        | first :: rest => rest.all (fun value => Value.sameType value first)
  | fuel + 1, .powerSet _ => true
termination_by value => sizeOf value
decreasing_by
  · simp_wf <;> omega
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_self _

mutual

def valueEqual : Nat → Value → Value → Except EvalError Bool
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, .integer left, .integer right => .ok (left == right)
  | fuel + 1, .boolean left, .boolean right => .ok (left == right)
  | fuel + 1, .atom leftCarrier leftName, .atom rightCarrier rightName =>
      .ok (leftCarrier == rightCarrier && leftName == rightName)
  | fuel + 1, .pair left₁ right₁, .pair left₂ right₂ => do
      let leftEqual ← valueEqual fuel left₁ left₂
      let rightEqual ← valueEqual fuel right₁ right₂
      pure (leftEqual && rightEqual)
  | fuel + 1, .set left, .set right => do
      let leftSubset ← subsetOf fuel left right
      let rightSubset ← subsetOf fuel right left
      pure (leftSubset && rightSubset)
  | fuel + 1, .integerSet, .integerSet
  | fuel + 1, .naturalSet, .naturalSet
  | fuel + 1, .natural1Set, .natural1Set
  | fuel + 1, .booleanSet, .booleanSet => .ok true
  | fuel + 1, .powerSet left, .powerSet right => .ok (left == right)
  | fuel + 1, _, _ => .ok false

def memberOf : Nat → Value → List Value → Except EvalError Bool
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, value, [] => .ok false
  | fuel + 1, value, candidate :: candidates => do
      let equal ← valueEqual fuel value candidate
      if equal then .ok true else memberOf fuel value candidates

def subsetOf : Nat → List Value → List Value → Except EvalError Bool
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, left, right =>
      if left == right then .ok true
      else match left with
        | [] => .ok true
        | value :: values => do
            let present ← memberOf fuel value right
            if present then subsetOf fuel values right else .ok false

end

def Value.makeSet (values : List Value) : Except EvalError Value :=
  match values with
  | [] => .ok (.set [])
  | first :: rest =>
      if rest.all (fun value => Value.sameType value first) then .ok (.set values)
      else
        let actual := (rest.find? (fun value => !Value.sameType value first)).map Value.typeOf
          |>.getD first.typeOf
        .error (.typeMismatch first.typeOf actual)

def ValueType.ofTy : EventB.Typing.Ty → Option ValueType
  | .int => some .integer
  | .bool => some .boolean
  | .given name => some (.given name)
  | .pow element => (ValueType.ofTy element).map (some ·) |>.map .finiteSet
  | .prod left right => do
      let left ← ValueType.ofTy left
      let right ← ValueType.ofTy right
      pure (.pair left right)
  | .mvar _ => none

def Value.typeMatches (expected : ValueType) (actual : ValueType) : Bool :=
  ValueType.compatible expected actual

def Value.matchesTy (value : Value) (expected : EventB.Typing.Ty) : Bool :=
  match ValueType.ofTy expected with
  | some expected => Value.typeMatches expected value.typeOf
  | none => false

def Value.contains (fuel : Nat) (value collection : Value) : Except EvalError Bool :=
  if fuel == 0 then .error .fuelExhausted
  else match collection, value with
    | .set values, value =>
        if !Value.isWellFormed fuel collection || !Value.isWellFormed fuel value then
          .error .invalidValue
        else match values.head? with
          | some first =>
              if !Value.sameType first value then
                .error (.typeMismatch first.typeOf value.typeOf)
              else memberOf fuel value values
          | none => .ok false
    | .powerSet element, value@(.set values) =>
        if !Value.isWellFormed fuel value then .error .invalidValue
        else if values.all (fun candidate => ValueType.compatible candidate.typeOf element) then
          .ok true
        else .error (.typeMismatch collection.typeOf value.typeOf)
    | .integerSet, .integer _ => .ok true
    | .naturalSet, .integer value => .ok (decide (0 ≤ value))
    | .natural1Set, .integer value => .ok (decide (0 < value))
    | .booleanSet, .boolean _ => .ok true
    | collection, value => .error (.typeMismatch collection.typeOf value.typeOf)

structure ValueEnv where
  values : List (String × Value) := []
  /-- Finite carrier observations. Given-set atoms are rejected unless their carrier
      and name occur here; arbitrary nominal tags are not a domain model. -/
  carriers : List (String × List String) := []
  deriving Repr, Inhabited, DecidableEq

def ValueEnv.lookup (env : ValueEnv) (name : String) : Option Value :=
  env.values.find? (·.1 == name) |>.map (·.2)

def ValueEnv.set (env : ValueEnv) (name : String) (value : Value) : ValueEnv :=
  { values := (name, value) :: env.values.filter (fun binding => binding.1 != name)
    carriers := env.carriers }

def ValueEnv.carrierContains (env : ValueEnv) (carrier name : String) : Bool :=
  match env.carriers.find? (·.1 == carrier) with
  | some (_, members) => members.contains name
  | none => false

def ValueEnv.valueIsWellFormed : Nat → ValueEnv → Value → Bool
  | 0, _, _ => false
  | fuel + 1, env, .atom carrier name => env.carrierContains carrier name
  | fuel + 1, env, .pair left right => valueIsWellFormed fuel env left &&
      valueIsWellFormed fuel env right
  | fuel + 1, env, .set values => values.all (valueIsWellFormed fuel env) &&
      match values with
      | [] => true
      | first :: rest => rest.all (fun value => Value.sameType value first)
  | fuel + 1, _, .powerSet _ => true
  | fuel + 1, _, .integer _ | fuel + 1, _, .boolean _ | fuel + 1, _, .integerSet |
      fuel + 1, _, .naturalSet | fuel + 1, _, .natural1Set | fuel + 1, _, .booleanSet => true
termination_by fuel => fuel
decreasing_by
  all_goals omega

def ValueEnv.declaredType? (declarations : List (String × EventB.Typing.Ty))
    (name : String) : Option EventB.Typing.Ty :=
  declarations.find? (·.1 == name) |>.map (·.2)

def ValueEnv.validateFuel (fuel : Nat) (declarations : List (String × EventB.Typing.Ty))
    (env : ValueEnv) : Except EvalError Unit := do
  let declarationNames := declarations.map (·.1)
  let envNames := env.values.map (·.1)
  if let some duplicate := declarationNames.find? (fun name => declarationNames.count name > 1) then
    .error (.duplicateAssignment duplicate)
  else if let some duplicate := envNames.find? (fun name => envNames.count name > 1) then
    .error (.duplicateAssignment duplicate)
  else
    for (name, ty) in declarations do
      let some expected := ValueType.ofTy ty | .error .invalidValue
      let some value := env.lookup name | .error (.unbound name)
      if !ValueEnv.valueIsWellFormed fuel env value then .error .invalidValue
      else if !Value.typeMatches expected value.typeOf then
        .error (.typeMismatch expected value.typeOf)
    if !env.values.all (fun (name, _) => declarationNames.contains name) then
      .error .invalidValue
    else .ok ()

def ValueEnv.validate (declarations : List (String × EventB.Typing.Ty))
    (env : ValueEnv) : Except EvalError Unit :=
  ValueEnv.validateFuel 128 declarations env

def ValueEnv.validationOk (fuel : Nat) (declarations : List (String × EventB.Typing.Ty))
    (env : ValueEnv) : Bool :=
  match ValueEnv.validateFuel fuel declarations env with
  | .ok () => true
  | .error _ => false

def valueMatches (actual expected : Value) : Bool :=
  match valueEqual 128 actual expected with
  | .ok result => result
  | .error _ => false

def ValueEnv.lookupMatches (env : ValueEnv) (name : String) (expected : Value) : Bool :=
  match env.lookup name with
  | some actual => valueMatches actual expected
  | none => false

private structure BeforeAfter where
  before : ValueEnv
  after : ValueEnv
  deriving Repr

/- A transition consumed by typed semantics carries the declaration domain. The
   evaluator revalidates both environments at the requested fuel, so a forged record
   cannot turn primed lookup into an unchecked state observation. -/
structure CheckedBeforeAfter where
  before : ValueEnv
  after : ValueEnv
  declarations : List (String × EventB.Typing.Ty)
  deriving Repr, DecidableEq

private def exceptDecEq {α β : Type} [DecidableEq α] [DecidableEq β] :
    (left right : Except α β) → Decidable (left = right)
  | .error left, .error right =>
      match decEq left right with
      | isTrue equal => isTrue (by cases equal; rfl)
      | isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .ok left, .ok right =>
      match decEq left right with
      | isTrue equal => isTrue (by cases equal; rfl)
      | isFalse unequal => isFalse (by intro proof; cases proof; exact unequal rfl)
  | .error _, .ok _ | .ok _, .error _ => isFalse (by intro proof; cases proof)

instance : DecidableEq (Except EvalError Bool) := exceptDecEq
instance : DecidableEq (Except EvalError CheckedBeforeAfter) := exceptDecEq

def CheckedBeforeAfter.make (fuel : Nat)
    (declarations : List (String × EventB.Typing.Ty))
    (before after : ValueEnv) : Except EvalError CheckedBeforeAfter := do
  if before.carriers != after.carriers then .error .invalidValue
  ValueEnv.validateFuel fuel declarations before
  ValueEnv.validateFuel fuel declarations after
  pure { before, after, declarations }

private structure EvalView where
  before : ValueEnv
  after : Option ValueEnv := none

private theorem xPrimeEndsWith : "x'".endsWith "'" = true := by native_decide
private theorem xEndsWith : "x".endsWith "'" = false := by native_decide
private theorem xPrimeBase : ("x'".dropEnd 1).copy = "x" := by native_decide

private def EvalView.lookup (view : EvalView) (name : String) : Except EvalError Value :=
  if name.endsWith "'" then
    match view.after with
    | none => .error (.unsupported (.id name))
    | some after =>
        match after.lookup (name.dropEnd 1 |>.copy) with
        | some value => .ok value
        | none => .error (.unbound name)
  else
    match view.before.lookup name with
    | some value => .ok value
    | none => .error (.unbound name)

private def EvalView.bind (view : EvalView) (name : String) (value : Value) : EvalView :=
  if name.endsWith "'" then
    let base := (name.dropEnd 1).copy
    { view with after := some ((view.after.getD view.before).set base value) }
  else
    { view with before := view.before.set name value }

/- Binder evaluation is deliberately one-sided: these finite witness candidates
   can establish an existential, but failure to find one is reported unsupported
   rather than falsely reported as a negative result. -/
private def binderCandidate (view : EvalView) : EventB.Formula.Term → Option Value
  | .id "ℤ" | .id "ℕ" => some (.integer 0)
  | .id "ℕ1" => some (.integer 1)
  | .id "BOOL" => some (.boolean true)
  | .id carrier =>
      match view.before.carriers.find? (·.1 == carrier) with
      | some (_, name :: _) => some (.atom carrier name)
      | _ => none
  | _ => none

def filterSetByMembership : Nat → String → List Value → List Value → Except EvalError (List Value)
  | 0, _, _, _ => .error .fuelExhausted
  | fuel + 1, _, [], _ => .ok []
  | fuel + 1, op, value :: values, right => do
      let present ← memberOf fuel value right
      let rest ← filterSetByMembership fuel op values right
      if (op == "∩" && present) || (op == "∖" && !present) then
        .ok (value :: rest)
      else .ok rest

private def relationValidateFunction : Nat → List Value → Except EvalError Unit
  | 0, _ => .error .fuelExhausted
  | fuel + 1, [] => .ok ()
  | fuel + 1, relation :: relations =>
      match relation with
      | .pair input _ => do
          let laterInputs := relations.filterMap fun value =>
            match value with
            | .pair laterInput _ => some laterInput
            | _ => none
          let duplicate ← memberOf fuel input laterInputs
          if duplicate then .error .invalidRelation
          else relationValidateFunction fuel relations
      | _ => .error .invalidRelation

private def relationType : Nat → List Value → Except EvalError (Option (ValueType × ValueType))
  | 0, _ => .error .fuelExhausted
  | fuel + 1, [] => .ok none
  | fuel + 1, .pair input output :: relations => do
      let rest ← relationType fuel relations
      match rest with
      | none => .ok (some (input.typeOf, output.typeOf))
      | some (inputType, outputType) =>
          if ValueType.compatible input.typeOf inputType &&
              ValueType.compatible output.typeOf outputType then
            .ok (some (inputType, outputType))
          else .error .invalidRelation
  | _, _ :: _ => .error .invalidRelation

private def relationApply : Nat → Value → List Value → Except EvalError (Option Value)
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, argument, [] => .ok none
  | fuel + 1, argument, relation :: relations =>
      match relation with
      | .pair input output => do
          let equal ← valueEqual fuel argument input
          if equal then
            let later ← relationApply fuel argument relations
            match later with
            | none => .ok (some output)
            | some _ => .error .invalidRelation
          else relationApply fuel argument relations
      | _ => .error .invalidRelation

private def relationImage : Nat → Value → List Value → Except EvalError (List Value)
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, argument, [] => .ok []
  | fuel + 1, argument, relation :: relations =>
      match relation with
      | .pair input output => do
          let equal ← valueEqual fuel argument input
          let rest ← relationImage fuel argument relations
          if equal then .ok (output :: rest) else .ok rest
      | _ => .error .invalidRelation

private def relationRestrict : Nat → Bool → List Value → List Value → Except EvalError (List Value)
  | 0, _, _, _ => .error .fuelExhausted
  | fuel + 1, _, [], _ => .ok []
  | fuel + 1, domain, relation :: relations, allowed =>
      match relation with
      | .pair input output => do
          let equal ← memberOf fuel (if domain then input else output) allowed
          let rest ← relationRestrict fuel domain relations allowed
          if equal then .ok (relation :: rest) else .ok rest
      | _ => .error .invalidRelation

private def relationDrop : Nat → Bool → List Value → List Value → Except EvalError (List Value)
  | 0, _, _, _ => .error .fuelExhausted
  | fuel + 1, _, [], _ => .ok []
  | fuel + 1, domain, relation :: relations, dropped =>
      match relation with
      | .pair input output => do
          let equal ← memberOf fuel (if domain then input else output) dropped
          let rest ← relationDrop fuel domain relations dropped
          if equal then .ok rest else .ok (relation :: rest)
      | _ => .error .invalidRelation

private def relationOverride : Nat → List Value → List Value → Except EvalError (List Value)
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, left, right => do
      let rightDomains ← right.mapM fun relation =>
        match relation with
        | .pair input _ => .ok input
        | _ => .error .invalidRelation
      let retained ← relationDrop fuel true left rightDomains
      .ok (retained ++ right)

mutual

private def evalValueFuel : Nat → EvalView → EventB.Formula.Term → Except EvalError Value
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, view, .id name =>
      if name == "ℤ" then .ok .integerSet
      else if name == "ℕ" then .ok .naturalSet
      else if name == "ℕ1" then .ok .natural1Set
      else if name == "BOOL" then .ok .booleanSet
      else do
        let value ← view.lookup name
        let env := if name.endsWith "'" then view.after.getD view.before else view.before
        if ValueEnv.valueIsWellFormed (fuel + 1) env value then
          .ok value
        else .error .invalidValue
  | fuel + 1, _, .num value => .ok (.integer value)
  | fuel + 1, view, .pre "−" term => do
      let value ← evalValueFuel fuel view term
      match value with
      | .integer value => .ok (.integer (-value))
      | value => .error (.typeMismatch .integer value.typeOf)
  | fuel + 1, view, .pre "ℙ" term => do
      let value ← evalValueFuel fuel view term
      match value with
      | .integerSet | .naturalSet | .natural1Set => .ok (.powerSet .integer)
      | .booleanSet => .ok (.powerSet .boolean)
      | .powerSet element => .ok (.powerSet (.finiteSet (some element)))
      | value => .error (.typeMismatch (.finiteSet none) value.typeOf)
  | fuel + 1, view, .bin op left right =>
      match op with
      | "↦" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          pure (.pair left right)
      | "+" | "−" | "∗" | "÷" | "mod" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .integer value => some value | _ => none)
            | .error (.typeMismatch .integer left.typeOf)
          let some right := (match right with | .integer value => some value | _ => none)
            | .error (.typeMismatch .integer right.typeOf)
          if op == "+" then .ok (.integer (left + right))
          else if op == "−" then .ok (.integer (left - right))
          else if op == "∗" then .ok (.integer (left * right))
          else if right == 0 then .error .divisionByZero
          else if op == "÷" then .ok (.integer (left / right))
          else .ok (.integer (left % right))
      | "∪" | "∩" | "∖" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) left.typeOf)
          let some right := (match right with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) right.typeOf)
          if !ValueType.compatible (Value.setType left) (Value.setType right) then
            .error (.typeMismatch (Value.setType left) (Value.setType right))
          else if op == "∪" then Value.makeSet (left ++ right)
          else do
            let values ← filterSetByMembership fuel op left right
            Value.makeSet values
      | "◁" | "⩤" | "▷" | "⩥" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) left.typeOf)
          let some right := (match right with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) right.typeOf)
          let domain := op == "◁" || op == "⩤"
          let relation := if domain then right else left
          let allowed := if domain then left else right
          let relationType ← relationType fuel relation
          if let some (inputType, outputType) := relationType then
            let selectedType := if domain then inputType else outputType
            if !ValueType.compatible (Value.setType allowed)
                (.finiteSet (some selectedType)) then
              .error (.typeMismatch (.finiteSet (some selectedType)) (Value.setType allowed))
          let values ← if op == "⩤" || op == "⩥" then
              relationDrop fuel domain relation allowed
            else relationRestrict fuel domain relation allowed
          Value.makeSet values
      | "" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) left.typeOf)
          let some right := (match right with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) right.typeOf)
          let leftType ← relationType fuel left
          let rightType ← relationType fuel right
          match leftType, rightType with
          | some (leftInput, leftOutput), some (rightInput, rightOutput) =>
              if !ValueType.compatible leftInput rightInput ||
                  !ValueType.compatible leftOutput rightOutput then
                .error (.typeMismatch (.pair leftInput leftOutput)
                  (.pair rightInput rightOutput))
          | _, _ => pure ()
          relationOverride fuel left right >>= Value.makeSet
      | "," => .error (.unsupported (.bin op left right))
      | _ => .error (.unsupported (.bin op left right))
  | fuel + 1, view, .set values => do
      let values ← evalValueListFuel fuel view values
      Value.makeSet values
  | fuel + 1, view, .app function argument => do
      let function ← evalValueFuel fuel view function
      let argument ← evalValueFuel fuel view argument
      let some relation := (match function with | .set values => some values | _ => none)
        | .error (.typeMismatch (.finiteSet none) function.typeOf)
      let relationType ← relationType fuel relation
      relationValidateFunction fuel relation
      if let some (inputType, _) := relationType then
        if !ValueType.compatible inputType argument.typeOf then
          .error (.typeMismatch inputType argument.typeOf)
      let result ← relationApply fuel argument relation
      match result with
      | some value => .ok value
      | none => .error .partialApplication
  | fuel + 1, view, .img relation argument => do
      let relation ← evalValueFuel fuel view relation
      let argument ← evalValueFuel fuel view argument
      let some relation := (match relation with | .set values => some values | _ => none)
        | .error (.typeMismatch (.finiteSet none) relation.typeOf)
      let relationType ← relationType fuel relation
      if let some (inputType, _) := relationType then
        if !ValueType.compatible inputType argument.typeOf then
          .error (.typeMismatch inputType argument.typeOf)
      let values ← relationImage fuel argument relation
      Value.makeSet values
  | _, _, term => .error (.unsupported term)

private def evalValueListFuel : Nat → EvalView → List EventB.Formula.Term →
    Except EvalError (List Value)
  | 0, _, _ => .error .fuelExhausted
  | _fuel + 1, _, [] => .ok []
  | fuel + 1, view, term :: terms => do
      let value ← evalValueFuel fuel view term
      let values ← evalValueListFuel fuel view terms
      pure (value :: values)

private def evalPredicateFuel : Nat → EvalView → EventB.Formula.Term → Except EvalError Bool
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, _, .id "⊤" => .ok true
  | fuel + 1, _, .id "⊥" => .ok false
  | fuel + 1, view, .id name =>
      match view.lookup name with
      | .ok (.boolean value) => .ok value
      | .ok value => .error (.typeMismatch .boolean value.typeOf)
      | .error error => .error error
  | fuel + 1, view, .pre "¬" term => do
      let value ← evalPredicateFuel fuel view term
      pure !value
  | fuel + 1, view, term@(.bind "∃" (.bin "⦂" (.id name) type) body) =>
      match binderCandidate view type with
      | none => .error (.unsupported term)
      | some witness =>
          match evalPredicateFuel fuel (view.bind name witness) body with
          | .ok true => .ok true
          | .ok false => .error (.unsupported term)
          | .error error => .error error
  | fuel + 1, view, term@(.app (.id "finite") argument) => do
      let value ← evalValueFuel fuel view argument
      match value with
      | .set _ => .ok true
      | .powerSet _ | .integerSet | .naturalSet | .natural1Set | .booleanSet => .ok false
      | value => .error (.typeMismatch (.finiteSet none) value.typeOf)
  | fuel + 1, view, .bin op left right =>
      match op with
      | "∧" | "∨" | "⇒" | "⇔" => do
          let left ← evalPredicateFuel fuel view left
          let right ← evalPredicateFuel fuel view right
          if op == "∧" then .ok (left && right)
          else if op == "∨" then .ok (left || right)
          else if op == "⇒" then .ok (!left || right)
          else .ok (left == right)
      | "=" | "≠" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          if !left.sameType right then .error (.typeMismatch left.typeOf right.typeOf)
          else do
            let equal ← valueEqual fuel left right
            .ok (if op == "=" then equal else !equal)
      | "<" | "≤" | ">" | "≥" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .integer value => some value | _ => none)
            | .error (.typeMismatch .integer left.typeOf)
          let some right := (match right with | .integer value => some value | _ => none)
            | .error (.typeMismatch .integer right.typeOf)
          .ok (if op == "<" then decide (left < right)
            else if op == "≤" then decide (left ≤ right)
            else if op == ">" then decide (left > right)
            else decide (left ≥ right))
      | "∈" | "∉" => do
          let value ← evalValueFuel fuel view left
          let collection ← evalValueFuel fuel view right
          let result ← Value.contains fuel value collection
          .ok (if op == "∈" then result else !result)
      | "⊆" | "⊈" | "⊂" | "⊄" => do
          let left ← evalValueFuel fuel view left
          let right ← evalValueFuel fuel view right
          let some left := (match left with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) left.typeOf)
          let some right := (match right with | .set values => some values | _ => none)
            | .error (.typeMismatch (.finiteSet none) right.typeOf)
          if !ValueType.compatible (Value.setType left) (Value.setType right) then
            .error (.typeMismatch (Value.setType left) (Value.setType right))
          else
            let leftSubset ← subsetOf fuel left right
            let rightSubset ← subsetOf fuel right left
            let subset := if op == "⊆" || op == "⊈" then leftSubset
              else leftSubset && !rightSubset
            .ok (if op == "⊆" || op == "⊂" then subset else !subset)
      | "↔" => .error (.unsupported (.bin op left right))
      | _ => .error (.unsupported (.bin op left right))
  | _, _, term => .error (.unsupported term)

end

private def evalValueWithFuel (fuel : Nat) (env : ValueEnv)
    (term : EventB.Formula.Term) : Except EvalError Value :=
  evalValueFuel fuel { before := env } term

private def evalPredicateWithFuel (fuel : Nat) (env : ValueEnv)
    (term : EventB.Formula.Term) : Except EvalError Bool :=
  evalPredicateFuel fuel { before := env } term

/- Public, error-aware wrappers keep the recursive evaluator implementation private while
   allowing typed adequacy fixtures to name the exact fuel they validate. -/
def evalValueAtFuel (fuel : Nat) (env : ValueEnv)
    (term : EventB.Formula.Term) : Except EvalError Value :=
  evalValueWithFuel fuel env term

def evalPredicateAtFuel (fuel : Nat) (env : ValueEnv)
    (term : EventB.Formula.Term) : Except EvalError Bool :=
  evalPredicateWithFuel fuel env term

/-- Complete existential evaluation only over a caller-supplied finite domain.
    The ordinary binder evaluator remains deliberately one-sided for infinite or
    implicit Event-B types; this API makes the completeness boundary explicit. -/
def evalPredicateOverFiniteDomain (fuel : Nat) (env : ValueEnv) (binder : String)
    (candidates : List Value) (body : EventB.Formula.Term) : Except EvalError Bool :=
  match candidates with
  | [] => .ok false
  | candidate :: rest =>
      match evalPredicateAtFuel fuel (env.set binder candidate) body with
      | .ok true => .ok true
      | .ok false => evalPredicateOverFiniteDomain fuel env binder rest body
      | .error error => .error error
termination_by candidates.length

theorem evalPredicateOverFiniteDomain_true (fuel : Nat) (env : ValueEnv)
    (binder : String) (candidates : List Value) (body : EventB.Formula.Term)
    (evaluated : evalPredicateOverFiniteDomain fuel env binder candidates body = .ok true) :
    ∃ candidate, candidate ∈ candidates ∧
      evalPredicateAtFuel fuel (env.set binder candidate) body = .ok true := by
  induction candidates with
  | nil => simp [evalPredicateOverFiniteDomain] at evaluated
  | cons candidate rest inductionHypothesis =>
      simp only [evalPredicateOverFiniteDomain] at evaluated
      cases head : evalPredicateAtFuel fuel (env.set binder candidate) body with
      | error error => simp [head] at evaluated
      | ok result =>
          cases result with
          | false =>
              obtain ⟨witness, member, holds⟩ :=
                inductionHypothesis (by simpa [head] using evaluated)
              exact ⟨witness, by simp [member], holds⟩
          | true => exact ⟨candidate, by simp, head⟩

theorem ValueEnv.lookup_set_self (env : ValueEnv) (name : String) (value : Value) :
    (env.set name value).lookup name = some value := by
  simp [ValueEnv.lookup, ValueEnv.set]

theorem evalWitnessIntegerZeroDivOne (env : ValueEnv) :
    evalPredicateAtFuel 128 env
      (.bind "∃" (.bin "⦂" (.id "p") (.id "ℤ"))
        (.bin "=" (.id "p") (.bin "÷" (.num 0) (.num 1)))) = .ok true := by
  have pNotPrime : "p".endsWith "'" = false := by native_decide
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
    native_decide
  simp [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel,
    evalValueFuel, binderCandidate, EvalView.bind, EvalView.lookup,
    ValueEnv.lookup, ValueEnv.set, ValueEnv.lookup_set_self, ValueEnv.valueIsWellFormed,
    Value.sameType, Value.typeOf,
    ValueType.compatible, valueEqual, integerCompatible, pNotPrime,
    Bind.bind, Except.bind]

theorem evalPredicateIntegerOneEqOne (env : ValueEnv) :
    evalPredicateAtFuel 128 env (.bin "=" (.num 1) (.num 1)) = .ok true := by
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
    native_decide
  simp [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel,
    evalValueFuel, Value.sameType, Value.typeOf, ValueType.compatible,
    valueEqual, integerCompatible, Bind.bind, Except.bind]

theorem evalPredicateIntegerOneNeZero (env : ValueEnv) :
    evalPredicateAtFuel 128 env (.bin "≠" (.num 1) (.num 0)) = .ok true := by
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
    native_decide
  simp [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel,
    evalValueFuel, Value.sameType, Value.typeOf, ValueType.compatible,
    valueEqual, integerCompatible, Bind.bind, Except.bind]

theorem evalPredicateFiniteZero (env : ValueEnv) :
    evalPredicateAtFuel 128 env (.app (.id "finite") (.set [.num 0])) = .ok true := by
  have values : evalValueListFuel 126 { before := env } [.num 0] = .ok [.integer 0] := by
    simp [evalValueListFuel, evalValueFuel, Bind.bind, Except.bind]
    rfl
  simp [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel, evalValueFuel,
    values, Value.makeSet, Value.sameType, Value.typeOf, ValueType.compatible,
    Bind.bind, Except.bind]

theorem evalValueFiniteZero (env : ValueEnv) :
    evalValueAtFuel 128 env (.set [.num 0]) = .ok (.set [.integer 0]) := by
  have values : evalValueListFuel 127 { before := env } [.num 0] = .ok [.integer 0] := by
    simp [evalValueListFuel, evalValueFuel, Bind.bind, Except.bind]
    rfl
  simpa [evalValueAtFuel, evalValueWithFuel, evalValueFuel, values,
    Value.makeSet, Value.sameType, Value.typeOf, ValueType.compatible,
    Bind.bind, Except.bind]

theorem evalValueIdentifierSingletonZero :
    evalValueAtFuel 127 { values := [("S", .set [.integer 0])] } (.id "S") =
      .ok (.set [.integer 0]) := by
  have xNotEndsWith : ¬ "S".endsWith "'" = true := by native_decide
  simp [evalValueAtFuel, evalValueWithFuel, evalValueFuel, EvalView.lookup,
    ValueEnv.lookup, ValueEnv.valueIsWellFormed, xNotEndsWith, Bind.bind, Except.bind]

def evalBeforeAfter (fuel : Nat) (transition : CheckedBeforeAfter)
    (term : EventB.Formula.Term) : Except EvalError Bool :=
  if ValueEnv.validationOk fuel transition.declarations transition.before &&
      ValueEnv.validationOk fuel transition.declarations transition.after then
    evalPredicateFuel fuel { before := transition.before, after := some transition.after } term
  else .error .invalidValue

theorem evalBeforeAfterIntegerOneOrOne
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true) :
    evalBeforeAfter 128 transition
      (.bin "∨" (.bin "=" (.num 1) (.num 1))
        (.bin "=" (.num 1) (.num 1))) = .ok true := by
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
    native_decide
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    Value.sameType, Value.typeOf, ValueType.compatible, valueEqual, integerCompatible,
    Bind.bind, Except.bind]

theorem evalBeforeAfterZeroSetNeEmpty
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true) :
    evalBeforeAfter 128 transition
      (.bin "≠" (.set [.num 0]) (.set [])) = .ok true := by
  have leftValues :
      evalValueListFuel 126 { before := transition.before, after := some transition.after }
          [.num 0] = .ok [.integer 0] := by
    simp [evalValueListFuel, evalValueFuel, Bind.bind, Except.bind]
    rfl
  have rightValues :
      evalValueListFuel 126 { before := transition.before, after := some transition.after }
          [] = .ok [] := by
    simp [evalValueListFuel, evalValueFuel, Bind.bind, Except.bind]
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    leftValues, rightValues,
    Value.makeSet, ValueEnv.lookup, Value.sameType, Value.typeOf, ValueType.compatible,
    Value.contains, memberOf, subsetOf, valueEqual, Bind.bind, Except.bind]
  rfl

theorem evalBeforeAfterZeroSetSubset
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true) :
    evalBeforeAfter 128 transition
      (.bin "⊆" (.set [.num 0]) (.set [.num 0])) = .ok true := by
  have values :
      evalValueListFuel 126 { before := transition.before, after := some transition.after }
          [.num 0] = .ok [.integer 0] := by
    simp [evalValueListFuel, evalValueFuel, Bind.bind, Except.bind]
    rfl
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by rfl
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    values, Value.makeSet, Value.setType, Value.sameType, Value.typeOf, ValueType.compatible,
    Value.contains, memberOf, subsetOf, valueEqual, integerCompatible, Bind.bind, Except.bind]

private theorem valueTypeCompatibleSelf : ∀ valueType : ValueType,
    valueType.compatible valueType = true := by
  intro valueType
  cases valueType with
  | integer => rfl
  | boolean => rfl
  | given name => simp [ValueType.compatible]
  | finiteSet element =>
      cases element with
      | none => rfl
      | some element =>
          simp [ValueType.compatible, valueTypeCompatibleSelf element]
  | pair left right =>
      simp [ValueType.compatible, valueTypeCompatibleSelf left,
        valueTypeCompatibleSelf right]
termination_by valueType => sizeOf valueType
decreasing_by all_goals simp_wf <;> omega

theorem evalBeforeAfterIdentifierSubsetSelf
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (valueShape : ∃ values, evalValueAtFuel 127 transition.before (.id "S") =
      .ok (.set values))
    (afterEq : transition.after = transition.before) :
    evalBeforeAfter 128 transition
      (.bin "⊆" (.id "S") (.id "S")) = .ok true := by
  have xEndsWith : "S".endsWith "'" = false := by native_decide
  have xNotEndsWith : ¬ "S".endsWith "'" = true := by native_decide
  rcases valueShape with ⟨values, beforeShape⟩
  have beforeEval :
        evalValueFuel 127 { before := transition.before, after := some transition.after }
            (.id "S") = .ok (.set values) := by
      simpa [evalValueAtFuel, evalValueWithFuel, evalValueFuel, EvalView.lookup,
        ValueEnv.lookup, xEndsWith, xNotEndsWith] using
        beforeShape
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, beforeEval,
    ValueEnv.valueIsWellFormed, Value.setType, ValueType.compatible,
    valueTypeCompatibleSelf, subsetOf,
    Value.typeOf, memberOf, valueEqual, Bind.bind, Except.bind]

theorem evalBeforeAfterIdentifierType
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (beforeType : evalPredicateAtFuel 128 transition.before
      (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))) = .ok true) :
    evalBeforeAfter 128 transition
      (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))) = .ok true := by
  have xEndsWith : "S".endsWith "'" = false := by native_decide
  have xNotEndsWith : ¬ "S".endsWith "'" = true := by native_decide
  have beforeTypeEval :
      evalPredicateFuel 128 { before := transition.before, after := some transition.after }
          (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))) = .ok true := by
    simpa [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel,
      evalValueFuel, EvalView.lookup, ValueEnv.lookup, xEndsWith, xNotEndsWith,
      Bind.bind, Except.bind] using beforeType
  simp [evalBeforeAfter, beforeValid, afterValid, beforeTypeEval]

theorem evalBeforeAfterIdentifierFinite
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (beforeFinite : evalPredicateAtFuel 128 transition.before
      (.app (.id "finite") (.id "S")) = .ok true) :
    evalBeforeAfter 128 transition
      (.app (.id "finite") (.id "S")) = .ok true := by
  have xEndsWith : "S".endsWith "'" = false := by native_decide
  have xNotEndsWith : ¬ "S".endsWith "'" = true := by native_decide
  have beforeFiniteEval :
      evalPredicateFuel 128 { before := transition.before, after := some transition.after }
          (.app (.id "finite") (.id "S")) = .ok true := by
    simpa [evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel,
      evalValueFuel, EvalView.lookup, ValueEnv.lookup, xEndsWith, xNotEndsWith,
      Bind.bind, Except.bind] using beforeFinite
  simp [evalBeforeAfter, beforeValid, afterValid, beforeFiniteEval]

theorem evalBeforeAfterZeroNat
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true) :
    evalBeforeAfter 128 transition
      (.bin "∈" (.num 0) (.id "ℕ")) = .ok true := by
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    Value.contains, Bind.bind, Except.bind]

theorem evalBeforeAfterZeroLeZero
    (transition : CheckedBeforeAfter)
    (beforeValid : ValueEnv.validationOk 128 transition.declarations transition.before = true)
    (afterValid : ValueEnv.validationOk 128 transition.declarations transition.after = true) :
    evalBeforeAfter 128 transition
      (.bin "≤" (.num 0) (.num 0)) = .ok true := by
  simp [evalBeforeAfter, beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    Bind.bind, Except.bind]

def assignmentPredicateWithFuel (fuel : Nat) (transition : CheckedBeforeAfter)
    (predicate : EventB.Formula.Term) : Prop :=
  evalBeforeAfter fuel transition predicate = .ok true

def assignmentPredicate (transition : CheckedBeforeAfter)
    (predicate : EventB.Formula.Term) : Prop :=
  assignmentPredicateWithFuel 128 transition predicate

/-- The executable before/after evaluator turns an integer EQL equality into the
    corresponding equality of the two checked integer observations. -/
theorem eqlIntegerAfterEqBefore
    (fuel : Nat) (name : String) (transition : CheckedBeforeAfter)
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
    (evaluated : assignmentPredicateWithFuel fuel transition
      (.bin "=" (.id (name ++ "'")) (.id name))) :
    afterValue = beforeValue := by
  have primeEndsWith : (name ++ "'").endsWith "'" = true := by
    rw [String.endsWith_eq_endsWith_toSlice]
    rw [String.Slice.endsWith_string_iff]
    simpa using (List.suffix_append name.toList ("'" : String).toList)
  have beforeLookup' := beforeLookup
  have afterLookup' := afterLookup
  simp only [ValueEnv.lookup] at beforeLookup'
  simp [primedBase] at afterLookup'
  simp only [ValueEnv.lookup] at afterLookup'
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by rfl
  cases fuel with
  | zero =>
      simp [assignmentPredicateWithFuel, evalBeforeAfter, evalPredicateFuel,
        beforeValid, afterValid] at evaluated
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [assignmentPredicateWithFuel, evalBeforeAfter, evalPredicateFuel,
            evalValueFuel, Bind.bind, Except.bind, beforeValid, afterValid] at evaluated
      | succ fuel =>
          cases fuel with
          | zero =>
              have equal : (afterValue == beforeValue) = true := by
                simpa [assignmentPredicateWithFuel, evalBeforeAfter, evalPredicateFuel,
                  evalValueFuel, EvalView.lookup, ValueEnv.lookup,
                  ValueEnv.valueIsWellFormed, Bind.bind, Except.bind, valueEqual,
                  Value.sameType, Value.typeOf, ValueType.compatible, beq_iff_eq,
                  integerCompatible,
                  beforeLookup', afterLookup', beforeValid, afterValid,
                  unprimed, primedBase, primeEndsWith,
                  primeNotInteger, primeNotNatural, primeNotNatural1, primeNotBoolean,
                  notInteger, notNatural, notNatural1, notBoolean] using evaluated
              exact eq_of_beq equal
          | succ fuel =>
              have equal : (afterValue == beforeValue) = true := by
                simpa [assignmentPredicateWithFuel, evalBeforeAfter, evalPredicateFuel,
                  evalValueFuel, EvalView.lookup, ValueEnv.lookup,
                  ValueEnv.valueIsWellFormed, beforeLookup', afterLookup',
                  Bind.bind, Except.bind, Value.sameType, Value.typeOf,
                  ValueType.compatible, beq_iff_eq, valueEqual, beforeValid, afterValid,
                  integerCompatible,
                  unprimed, primedBase, primeEndsWith, primeNotInteger, primeNotNatural,
                  primeNotNatural1, primeNotBoolean, notInteger, notNatural, notNatural1,
                  notBoolean] using evaluated
              exact eq_of_beq equal

def evalValue : ValueEnv → EventB.Formula.Term → Except EvalError Value :=
  evalValueWithFuel 128

def evalPredicate : ValueEnv → EventB.Formula.Term → Except EvalError Bool :=
  evalPredicateWithFuel 128

#guard match evalValue
    { values := [("f", .set [.pair (.integer 0) (.integer 1)])] }
    (.app (.id "f") (.num 0)) with
  | .ok (.integer 1) => true
  | _ => false
#guard match evalValue
    { values := [("f", .set [.pair (.integer 0) (.integer 1)]), ("b", .boolean true)] }
    (.app (.id "f") (.id "b")) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalValue
    { values := [("f", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 1) (.integer 2)])] }
    (.img (.id "f") (.num 1)) with
  | .ok (.set [.integer 2]) => true
  | _ => false
#guard match evalValue
    { values := [("r", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 1) (.integer 2)])] }
    (.bin "◁" (.set [.num 1]) (.id "r")) with
  | .ok (.set [.pair (.integer 1) (.integer 2)]) => true
  | _ => false
#guard match evalValue
    { values := [("r", .set [.pair (.integer 0) (.integer 1)]), ("b", .boolean true)],
      carriers := [] }
    (.bin "◁" (.set [(.id "b")]) (.id "r")) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalValue
    { values := [("r", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 1) (.integer 2)])] }
    (.bin "⩤" (.set [.num 1]) (.id "r")) with
  | .ok (.set [.pair (.integer 0) (.integer 1)]) => true
  | _ => false
#guard match evalValue
    { values := [("r", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 1) (.integer 2)])] }
    (.bin "⩥" (.id "r") (.set [.num 1])) with
  | .ok (.set [.pair (.integer 1) (.integer 2)]) => true
  | _ => false
#guard match evalValue
    { values := [("r", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 1) (.integer 2)])] }
    (.bin "" (.id "r") (.set [.bin "↦" (.num 0) (.num 3)])) with
  | .ok (.set [.pair (.integer 1) (.integer 2), .pair (.integer 0) (.integer 3)]) => true
  | _ => false
#guard match evalValue
    { values := [("f", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 0) (.integer 2)])] }
    (.app (.id "f") (.num 0)) with
  | .error .invalidRelation => true
  | _ => false
#guard match evalValue
    { values := [("f", .set [.pair (.integer 0) (.integer 1),
      .pair (.integer 0) (.integer 2)])] }
    (.app (.id "f") (.num 9)) with
  | .error .invalidRelation => true
  | _ => false
private def ValueEnv.parallelAssign (env : ValueEnv)
    (updates : List (String × EventB.Formula.Term)) : Except EvalError BeforeAfter := do
  let names := updates.map (·.1)
  if let some duplicate := names.find? (fun name => names.count name > 1) then
    .error (.duplicateAssignment duplicate)
  else if let some invalid := names.find? (fun name => name.isEmpty || name.endsWith "'") then
    .error (.invalidTarget invalid)
  else
    let values ← updates.mapM fun update => evalValue env update.2
    let after := updates.zip values |>.foldl
      (fun result ((name, _), value) => result.set name value) env
    pure { before := env, after := after }

private def ValueEnv.parallelAssignTerms (env : ValueEnv)
    (targets : List String) (rhs : List EventB.Formula.Term) : Except EvalError BeforeAfter :=
  if targets.length != rhs.length then .error .assignmentArity
  else ValueEnv.parallelAssign env (targets.zip rhs)

def ValueEnv.parallelAssignTypedFuel (fuel : Nat)
    (declarations : List (String × EventB.Typing.Ty)) (env : ValueEnv)
    (updates : List (String × EventB.Formula.Term)) : Except EvalError CheckedBeforeAfter := do
  ValueEnv.validateFuel fuel declarations env
  let names := updates.map (·.1)
  if let some duplicate := names.find? (fun name => names.count name > 1) then
    .error (.duplicateAssignment duplicate)
  else
    for (name, _) in updates do
      if name.isEmpty || name.endsWith "'" then .error (.invalidTarget name)
      if (ValueEnv.declaredType? declarations name).isNone then
        .error (.invalidTarget name)
    let values ← updates.mapM fun (name, term) => do
      let value ← evalValueWithFuel fuel env term
      let some ty := ValueEnv.declaredType? declarations name | .error (.invalidTarget name)
      let some expected := ValueType.ofTy ty | .error .invalidValue
      if Value.typeMatches expected value.typeOf then pure value
      else .error (.typeMismatch expected value.typeOf)
    let after := updates.zip values |>.foldl
      (fun result ((name, _), value) => result.set name value) env
    CheckedBeforeAfter.make fuel declarations env after

def ValueEnv.parallelAssignTyped
    (declarations : List (String × EventB.Typing.Ty)) (env : ValueEnv)
    (updates : List (String × EventB.Formula.Term)) : Except EvalError CheckedBeforeAfter :=
  ValueEnv.parallelAssignTypedFuel 128 declarations env updates

def declarationNames (elem : EventB.Elem) (tag : String) : List String :=
  elem.children.filter (fun child => child.tag == "org.eventb.core." ++ tag)
    |>.filterMap (·.attr? "org.eventb.core.identifier")

def dedupTypedBindings (seen : List String) : List (String × EventB.Typing.Ty) →
    List (String × EventB.Typing.Ty)
  | [] => []
  | binding :: rest =>
      if seen.contains binding.1 then dedupTypedBindings seen rest
      else binding :: dedupTypedBindings (binding.1 :: seen) rest

structure ComponentValuation where
  component : String
  types : List (String × EventB.Typing.Ty)
  eventParams : List ((String × String) × List (String × EventB.Typing.Ty))
  variables : List String
  deriving Repr

def ComponentValuation.fromProject (theory : EventB.Theory.Env)
    (project : EventB.Typing.Project) (component : String) :
    Except EventB.Error ComponentValuation := do
  let details ← EventB.Typing.inferComponentDetailsCheckedIn theory project component
  unless details.diagnostics.isEmpty do
    throw (EventB.Error.typing
      (s!"component {component} has typing diagnostics: " ++
        String.intercalate "; " details.diagnostics))
  let (_, closureNames) := EventB.Typing.closure project [] component
  let variables := closureNames.flatMap fun name =>
    match EventB.Typing.lookupComponent project name with
    | some current => declarationNames current.elem "variable"
    | none => []
  let valuation : ComponentValuation :=
    { component := component
      types := details.types
      eventParams := details.eventParams
      variables := variables.eraseDups }
  pure valuation

def ComponentValuation.declarationsForEvent (valuation : ComponentValuation)
    (project : EventB.Typing.Project) (event : String) :
    List (String × EventB.Typing.Ty) :=
  let parameterNames := valuation.eventParams.flatMap (·.2.map (·.1))
  let globals := valuation.types.filter (fun binding => !parameterNames.contains binding.1)
  let eventBindings := EventB.Typing.visibleEventBindings project valuation.eventParams
    valuation.component event
  dedupTypedBindings [] (globals ++ eventBindings)

def ComponentValuation.validate (valuation : ComponentValuation)
    (project : EventB.Typing.Project) (event : String) (env : ValueEnv) :
    Except EvalError Unit :=
  ValueEnv.validate (valuation.declarationsForEvent project event) env

def deterministicActionAssignments (action : EventB.Elem) :
    Except EvalError (List (String × EventB.Formula.Term)) :=
  match action.attr? "org.eventb.core.assignment" with
  | none => .ok []
  | some source =>
      match EventB.Formula.parse source with
      | .error _ => .error (.unsupported (.id source))
      | .ok (.bin "≔" lhs rhs) =>
          let targets := EventB.Formula.flattenCommas lhs
          let values := EventB.Formula.flattenCommas rhs
          if targets.length != values.length then .error .assignmentArity
          else
            targets.zip values |>.mapM fun (target, value) =>
              match target with
              | .id name => .ok (name, value)
              | _ => .error (.invalidTarget (EventB.Formula.print target))
      | .ok term => .error (.unsupported term)

def ComponentValuation.eventAssignments (valuation : ComponentValuation)
    (project : EventB.Typing.Project) (event : String) :
    Except EvalError (List (String × EventB.Formula.Term)) :=
  match EventB.Typing.lookupComponent project valuation.component with
  | none => .error (.unbound valuation.component)
  | some component =>
      match component.elem.children.find? (fun candidate =>
          candidate.tag == "org.eventb.core.event" &&
            candidate.attr? "org.eventb.core.label" == some event) with
      | none => .error (.unbound event)
      | some eventElem =>
          EventB.POG.effectiveActions project valuation.component eventElem |>.flatMapM
            deterministicActionAssignments

def ComponentValuation.parallelAssign (valuation : ComponentValuation)
    (project : EventB.Typing.Project) (event : String) (env : ValueEnv)
    (updates : List (String × EventB.Formula.Term)) : Except EvalError CheckedBeforeAfter := do
  let expected ← valuation.eventAssignments project event
  if updates != expected then
    .error (.invalidTarget ("updates do not match effective actions of " ++ event))
  else if let some invalid := updates.find?
      (fun update => !valuation.variables.contains update.1) then
    .error (.invalidTarget invalid.1)
  else
    ValueEnv.parallelAssignTyped (valuation.declarationsForEvent project event) env updates

def assignmentRelation (fuel : Nat)
    (declarations : List (String × EventB.Typing.Ty)) (transition : CheckedBeforeAfter)
    (updates : List (String × EventB.Formula.Term)) : Prop :=
  transition.declarations = declarations ∧
    ValueEnv.validationOk fuel declarations transition.before = true ∧
    ValueEnv.validationOk fuel declarations transition.after = true ∧
    ValueEnv.parallelAssignTypedFuel fuel declarations transition.before updates = .ok transition

theorem assignmentRelation_x_self_zero :
    assignmentRelation 128 [("x", .int)]
      { before := { values := [("x", .integer 0)] }
        after := { values := [("x", .integer 0)] }
        declarations := [("x", .int)] }
      [("x", .id "x")] := by
  unfold assignmentRelation
  native_decide

theorem assignmentRelation_x_zero :
    assignmentRelation 128 [("x", .int)]
      { before := { values := [("x", .integer 0)] }
        after := { values := [("x", .integer 0)] }
        declarations := [("x", .int)] }
      [("x", .num 0)] := by
  unfold assignmentRelation
  native_decide

theorem assignmentRelation_x_one :
    assignmentRelation 128 [("x", .int)]
      { before := { values := [("x", .integer 1)] }
        after := { values := [("x", .integer 1)] }
        declarations := [("x", .int)] }
      [("x", .num 1)] := by
  unfold assignmentRelation
  native_decide

theorem assignmentPredicate_x_prime_in_zero :
    assignmentPredicateWithFuel 128
      { before := { values := [("x", .integer 0)] }
        after := { values := [("x", .integer 0)] }
        declarations := [("x", .int)] }
      (.bin "∈" (.id "x'") (.set [.num 0])) := by
  unfold assignmentPredicateWithFuel
  native_decide

theorem assignmentPredicate_x_in_integer_set :
    assignmentPredicateWithFuel 128
      { before := { values := [("x", .integer 0)] }
        after := { values := [("x", .integer 0)] }
        declarations := [("x", .int)] }
      (.bin "∈" (.id "x") (.id "ℤ")) := by
  unfold assignmentPredicateWithFuel
  native_decide

theorem assignmentPredicate_x_self_zero :
    assignmentPredicateWithFuel 128
      { before := { values := [("x", .integer 0)] }
        after := { values := [("x", .integer 0)] }
        declarations := [("x", .int)] }
      (.bin "=" (.id "x'") (.id "x")) := by
  unfold assignmentPredicateWithFuel
  native_decide

mutual

def supportsValue : EventB.Formula.Term → Bool
  | .id name => !name.endsWith "'"
  | .num _ => true
  | .pre "−" value => supportsValue value
  | .pre _ _ => false
  | .bin op left right =>
      (op == "↦" || op == "+" || op == "−" || op == "∗" ||
        op == "÷" || op == "mod" || op == "∪" || op == "∩" || op == "∖" ||
        op == "◁" || op == "⩤" || op == "▷" || op == "⩥" || op == "") &&
        supportsValue left && supportsValue right
  | .set values => supportsValueList values
  | .post _ _ | .bind _ _ _ => false
  | .app function argument | .img function argument =>
      supportsValue function && supportsValue argument

def supportsValueList : List EventB.Formula.Term → Bool
  | [] => true
  | value :: values => supportsValue value && supportsValueList values

end

#guard supportsValue (.app (.id "f") (.num 0))

def supportsPredicate : EventB.Formula.Term → Bool
  | .id _ => true
  | .pre "¬" predicate => supportsPredicate predicate
  | .pre _ _ => false
  | .bin op left right =>
      if op == "∧" || op == "∨" || op == "⇒" || op == "⇔" then
        supportsPredicate left && supportsPredicate right
      else if op == "=" || op == "≠" || op == "<" || op == "≤" || op == ">" ||
          op == "≥" || op == "∈" || op == "∉" || op == "⊆" || op == "⊈" ||
          op == "⊂" || op == "⊄" then
        supportsValue left && supportsValue right
      else false
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℤ")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℕ")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℕ1")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "BOOL")) body => supportsPredicate body
  | .app (.id "finite") argument => supportsValue argument
  | .num _ | .set _ | .post _ _ | .app _ _ | .img _ _ | .bind _ _ _ => false

#guard supportsPredicate (.app (.id "finite") (.id "S"))
#guard !supportsPredicate (.app (.id "finite") (.post "x" (.id "x")))
#guard match evalPredicate { values := [("S", .set [.integer 0])] }
    (.app (.id "finite") (.id "S")) with
  | .ok true => true
  | _ => false
#guard match evalPredicate {}
    (.app (.id "finite") (.id "ℤ")) with
  | .ok false => true
  | _ => false

mutual

def supportsBeforeAfterValue : EventB.Formula.Term → Bool
  | .id _ => true
  | .num _ => true
  | .pre "−" value => supportsBeforeAfterValue value
  | .pre _ _ => false
  | .bin op left right =>
      (op == "↦" || op == "+" || op == "−" || op == "∗" ||
        op == "÷" || op == "mod" || op == "∪" || op == "∩" || op == "∖" ||
        op == "◁" || op == "⩤" || op == "▷" || op == "⩥" || op == "") &&
        supportsBeforeAfterValue left && supportsBeforeAfterValue right
  | .set values => supportsBeforeAfterValueList values
  | .post _ _ | .bind _ _ _ => false
  | .app function argument | .img function argument =>
      supportsBeforeAfterValue function && supportsBeforeAfterValue argument

def supportsBeforeAfterValueList : List EventB.Formula.Term → Bool
  | [] => true
  | value :: values => supportsBeforeAfterValue value && supportsBeforeAfterValueList values

end

#guard supportsBeforeAfterValue (.img (.id "f") (.num 0))

#guard match evalPredicate
    { values := [("b", .boolean true)] }
    (.bin "⊆" (.set [.num 1]) (.set [.id "b"])) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalValue
    { values := [("b", .boolean true)] }
    (.bin "∖" (.set [.num 1]) (.set [.id "b"])) with
  | .error (.typeMismatch _ _) => true
  | _ => false

def supportsBeforeAfterPredicate : EventB.Formula.Term → Bool
  | .id _ => true
  | .pre "¬" predicate => supportsBeforeAfterPredicate predicate
  | .pre _ _ => false
  | .bin op left right =>
      if op == "∧" || op == "∨" || op == "⇒" || op == "⇔" then
        supportsBeforeAfterPredicate left && supportsBeforeAfterPredicate right
      else if op == "=" || op == "≠" || op == "<" || op == "≤" || op == ">" ||
          op == "≥" || op == "∈" || op == "∉" || op == "⊆" || op == "⊈" ||
          op == "⊂" || op == "⊄" then
        supportsBeforeAfterValue left && supportsBeforeAfterValue right
      else false
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℤ")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℕ")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "ℕ1")) body
  | .bind "∃" (.bin "⦂" (.id _) (.id "BOOL")) body => supportsBeforeAfterPredicate body
  | .app (.id "finite") argument => supportsBeforeAfterValue argument
  | .num _ | .set _ | .post _ _ | .app _ _ | .img _ _ | .bind _ _ _ => false

private def typedBindingProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "x ≔ 1")] []]] }]

private def badTypedBindingProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "bad"),
                      ("org.eventb.core.predicate", "missing = 0")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []] }]

#guard !Obligation.sourceBound typedBindingProject
  { component := "M", name := "INITIALISATION/x/EQL", kind := "EQL" }
#guard !Obligation.sourceBound typedBindingProject
  { component := "M", name := "INITIALISATION/y/EQL", kind := "EQL" }

#guard match ComponentValuation.fromProject EventB.Theory.empty typedBindingProject "M" with
  | .ok valuation =>
      valuation.types.any (fun binding => binding.1 == "x" && binding.2 == .int) &&
      valuation.variables.contains "x"
  | .error _ => false
#guard match ComponentValuation.fromProject EventB.Theory.empty typedBindingProject "M" with
  | .ok valuation =>
      match valuation.parallelAssign typedBindingProject "INITIALISATION"
          { values := [("x", .integer 0)] } [("x", .num 1)] with
      | .ok transition => transition.after.lookupMatches "x" (.integer 1)
      | .error _ => false
  | .error _ => false
#guard match ComponentValuation.fromProject EventB.Theory.empty badTypedBindingProject "M" with
  | .error error => error.kind == .typing
  | .ok _ => false
#guard match ComponentValuation.fromProject EventB.Theory.empty typedBindingProject "M" with
  | .ok valuation =>
      match valuation.parallelAssign typedBindingProject "MISSING"
          { values := [("x", .integer 0)] } [] with
      | .error (.unbound "MISSING") => true
      | _ => false
  | .error _ => false
#guard match ComponentValuation.fromProject EventB.Theory.empty typedBindingProject "M" with
  | .ok valuation =>
      match valuation.parallelAssign typedBindingProject "INITIALISATION"
          { values := [("x", .integer 0)] } [("x", .num 2)] with
      | .error (.invalidTarget _) => true
      | _ => false
  | .error _ => false

structure TypedFormulaModel where
  declarations : List (String × EventB.Typing.Ty)
  fuel : Nat
  wellFormed : ValueEnv → Prop
  /-- The semantic domain must contain an actual validated state; `False` is not a
      proof shortcut. -/
  inhabited : ∃ env, wellFormed env
  validated : ∀ env, wellFormed env → ValueEnv.validationOk fuel declarations env = true
  complete : ∀ env, ValueEnv.validationOk fuel declarations env = true → wellFormed env
  supports : EventB.Formula.Term → Bool

def TypedFormulaModel.denote (_model : TypedFormulaModel)
    (term : EventB.Formula.Term) (env : ValueEnv) : Prop :=
  evalPredicateAtFuel _model.fuel env term = .ok true

def TypedFormulaModel.on {τ : Type u} (model : TypedFormulaModel)
    (encode : τ → ValueEnv) : FormulaModel τ :=
  { denote := fun term state => model.denote term (encode state) }

def TypedFormulaModel.defined (_model : TypedFormulaModel)
    (term : EventB.Formula.Term) (env : ValueEnv) : Prop :=
  ∃ value, evalPredicateAtFuel _model.fuel env term = .ok value

def TypedFormulaModel.formulaModel (model : TypedFormulaModel) : FormulaModel ValueEnv :=
  { denote := model.denote }

def TypedFormulaModel.validUnchecked (model : TypedFormulaModel) (obligation : Obligation) : Prop :=
  if obligation.semanticShapeValid = true && obligation.valuationSupported = true then
    match obligation.kind, obligation.goal with
    | _, some goal =>
        model.supports goal = true ∧ obligation.hyps.all model.supports = true ∧
          ∀ env, model.wellFormed env →
            (model.defined goal env ∧
              ∀ hypothesis ∈ obligation.hyps, model.defined hypothesis env) ∧
            ((∀ hypothesis ∈ obligation.hyps, model.denote hypothesis env) →
              model.denote goal env)
    | "WWD", none =>
        obligation.hyps.all model.supports = true ∧
          ∀ env, model.wellFormed env →
            ∀ hypothesis ∈ obligation.hyps,
              model.defined hypothesis env ∧ model.denote hypothesis env
    | _, none => False
  else False

theorem TypedFormulaModel.valid_on
    {τ : Type u} (model : TypedFormulaModel) (encode : τ → ValueEnv)
    (obligation : Obligation)
    (valid : model.validUnchecked obligation)
    (wellFormed : ∀ state, model.wellFormed (encode state)) :
    FormulaModel.validUnchecked (model.on encode) obligation := by
  unfold TypedFormulaModel.validUnchecked at valid
  unfold FormulaModel.validUnchecked
  by_cases shape : obligation.semanticShapeValid = true
  · by_cases valuation : obligation.valuationSupported = true
    · cases goal : obligation.goal with
      | none =>
          by_cases wwd : obligation.kind = "WWD"
          · simp [shape, valuation, goal, wwd, TypedFormulaModel.on] at valid ⊢
            intro state hypothesis member
            rcases List.mem_map.1 member with ⟨term, termMember, rfl⟩
            exact (valid.2 (encode state) (wellFormed state) term termMember).2
          · simp [shape, valuation, goal, wwd] at valid ⊢
      | some target =>
          simp [shape, valuation, goal, TypedFormulaModel.on] at valid ⊢
          intro state hypotheses
          apply (valid.2.2 (encode state) (wellFormed state)).2
          intro term termMember
          exact hypotheses (fun state' => model.denote term (encode state'))
            (List.mem_map.mpr ⟨term, termMember, rfl⟩)
    · simp [TypedFormulaModel.validUnchecked, shape, valuation] at valid
  · simp [TypedFormulaModel.validUnchecked, shape] at valid

/- Formula validity over an explicit semantic state domain. Unlike the historical
   `validUnchecked` path, this does not pretend that every type-correct valuation is
   a reachable/invariant state; the caller must provide the domain and prove every
   encoded semantic state lies in it. -/
def TypedFormulaModel.validOnDomain
    (model : TypedFormulaModel) (domain : ValueEnv → Prop)
    (obligation : Obligation) : Prop :=
  if obligation.semanticShapeValid = true && obligation.valuationSupported = true then
    match obligation.kind, obligation.goal with
    | _, some goal =>
        model.supports goal = true ∧ obligation.hyps.all model.supports = true ∧
          ∀ env, domain env →
            (model.defined goal env ∧
              ∀ hypothesis ∈ obligation.hyps, model.defined hypothesis env) ∧
            ((∀ hypothesis ∈ obligation.hyps, model.denote hypothesis env) →
              model.denote goal env)
    | "WWD", none => obligation.hyps.all model.supports = true ∧
        ∀ env, domain env →
          ∀ hypothesis ∈ obligation.hyps,
            model.defined hypothesis env ∧ model.denote hypothesis env
    | _, none => False
  else False

theorem TypedFormulaModel.validOnDomain_on
    {τ : Type u} (model : TypedFormulaModel) (domain : ValueEnv → Prop)
    (encode : τ → ValueEnv) (obligation : Obligation)
    (valid : model.validOnDomain domain obligation)
    (stateDomain : ∀ state, domain (encode state)) :
    FormulaModel.validUnchecked (model.on encode) obligation := by
  unfold TypedFormulaModel.validOnDomain at valid
  unfold FormulaModel.validUnchecked
  by_cases shape : obligation.semanticShapeValid = true
  · by_cases valuation : obligation.valuationSupported = true
    · cases goal : obligation.goal with
      | none =>
          by_cases wwd : obligation.kind = "WWD"
          · simp [shape, valuation, goal, wwd, TypedFormulaModel.on] at valid ⊢
            intro state hypothesis member
            rcases List.mem_map.1 member with ⟨term, termMember, rfl⟩
            exact (valid.2 (encode state) (stateDomain state) term termMember).2
          · simp [shape, valuation, goal, wwd] at valid ⊢
      | some target =>
          simp [shape, valuation, goal, TypedFormulaModel.on] at valid ⊢
          intro state hypotheses
          apply (valid.2.2 (encode state) (stateDomain state)).2
          intro term termMember
          exact hypotheses (fun state' => model.denote term (encode state'))
            (List.mem_map.mpr ⟨term, termMember, rfl⟩)
    · simp [TypedFormulaModel.validOnDomain, shape, valuation] at valid
  · simp [TypedFormulaModel.validOnDomain, shape] at valid

def TypedFormulaModel.valid (model : TypedFormulaModel)
    (theory : EventB.Theory.Env) (project : EventB.Typing.Project)
    (obligation : Obligation) : Prop :=
  obligation.checkedIn theory project ∧
    (match EventB.Typing.inferComponentDetailsCheckedIn theory project obligation.component with
    | .ok details => model.declarations = details.types
    | .error _ => False) ∧
    (∀ env, ValueEnv.validationOk model.fuel model.declarations env = true →
      model.wellFormed env) ∧ model.validUnchecked obligation

structure TypedTransitionModel where
  fuel : Nat
  wellFormed : CheckedBeforeAfter → Prop
  inhabited : ∃ transition, wellFormed transition
  supports : EventB.Formula.Term → Bool

def TypedTransitionModel.denote (model : TypedTransitionModel)
    (term : EventB.Formula.Term) (transition : CheckedBeforeAfter) : Prop :=
  evalBeforeAfter model.fuel transition term = .ok true

def TypedTransitionModel.on {τ : Type u} (model : TypedTransitionModel)
    (encode : τ → CheckedBeforeAfter) : FormulaModel τ :=
  { denote := fun term state => model.denote term (encode state) }

def TypedTransitionModel.defined (model : TypedTransitionModel)
    (term : EventB.Formula.Term) (transition : CheckedBeforeAfter) : Prop :=
  ∃ value, evalBeforeAfter model.fuel transition term = .ok value

def TypedTransitionModel.validUnchecked (model : TypedTransitionModel)
    (obligation : Obligation) : Prop :=
  if obligation.semanticShapeValid = true && obligation.transitionValuationSupported = true then
    match obligation.goal with
    | some goal =>
        model.supports goal = true ∧ obligation.hyps.all model.supports = true ∧
          ∀ transition, model.wellFormed transition →
            (model.defined goal transition ∧
              ∀ hypothesis ∈ obligation.hyps, model.defined hypothesis transition) ∧
            ((∀ hypothesis ∈ obligation.hyps, model.denote hypothesis transition) →
              model.denote goal transition)
    | none => False
  else False

theorem TypedTransitionModel.valid_on
    {τ : Type u} (model : TypedTransitionModel)
    (encode : τ → CheckedBeforeAfter) (obligation : Obligation)
    (valid : model.validUnchecked obligation)
    (wellFormed : ∀ state, model.wellFormed (encode state)) :
    FormulaModel.validUnchecked (model.on encode) obligation := by
  unfold TypedTransitionModel.validUnchecked at valid
  unfold FormulaModel.validUnchecked
  by_cases shape : obligation.semanticShapeValid = true
  · by_cases valuation : obligation.transitionValuationSupported = true
    · cases goal : obligation.goal with
      | none =>
          simp [shape, valuation, goal] at valid ⊢
      | some target =>
          simp [shape, valuation, goal, TypedTransitionModel.on] at valid ⊢
          intro state hypotheses
          apply (valid.2.2 (encode state) (wellFormed state)).2
          intro term termMember
          exact hypotheses (fun state' => model.denote term (encode state'))
            (List.mem_map.mpr ⟨term, termMember, rfl⟩)
    · simp [TypedTransitionModel.validUnchecked, shape, valuation] at valid
  · simp [TypedTransitionModel.validUnchecked, shape] at valid

/- A source-bound transition domain is the missing bridge between a typed
   evaluator and a refinement event.  `validUnchecked` remains useful for
   local evaluator fixtures, but accepting adapters must quantify over the
   checked source relation rather than over an arbitrary singleton chosen by
   the evaluator author. -/
def TypedTransitionModel.validOnDomain
    (model : TypedTransitionModel)
    (domain : CheckedBeforeAfter → Prop)
    (obligation : Obligation) : Prop :=
  if obligation.semanticShapeValid = true && obligation.transitionValuationSupported = true then
    match obligation.goal with
    | some goal =>
        model.supports goal = true ∧ obligation.hyps.all model.supports = true ∧
          ∀ transition, domain transition →
            (model.defined goal transition ∧
              ∀ hypothesis ∈ obligation.hyps, model.defined hypothesis transition) ∧
            ((∀ hypothesis ∈ obligation.hyps, model.denote hypothesis transition) →
              model.denote goal transition)
    | none => False
  else False

theorem TypedTransitionModel.validOnDomain_on
    {τ : Type u} (model : TypedTransitionModel)
    (domain : CheckedBeforeAfter → Prop)
    (encode : τ → CheckedBeforeAfter) (obligation : Obligation)
    (valid : model.validOnDomain domain obligation)
    (domainValid : ∀ state, domain (encode state)) :
    FormulaModel.validUnchecked (model.on encode) obligation := by
  unfold TypedTransitionModel.validOnDomain at valid
  unfold FormulaModel.validUnchecked
  by_cases shape : obligation.semanticShapeValid = true
  · by_cases valuation : obligation.transitionValuationSupported = true
    · cases goal : obligation.goal with
      | none => simp [shape, valuation, goal] at valid ⊢
      | some target =>
          simp [shape, valuation, goal, TypedTransitionModel.on] at valid ⊢
          intro state hypotheses
          apply (valid.2.2 (encode state) (domainValid state)).2
          intro term termMember
          exact hypotheses (fun state' => model.denote term (encode state'))
            (List.mem_map.mpr ⟨term, termMember, rfl⟩)
    · simp [TypedTransitionModel.validOnDomain, shape, valuation] at valid
  · simp [TypedTransitionModel.validOnDomain, shape] at valid

structure TransitionSourceCoverage (τ : Type u) where
  encode : τ → CheckedBeforeAfter
  source : CheckedBeforeAfter → Prop
  sourceComplete : ∀ transition, source transition → ∃ state, encode state = transition

theorem TransitionSourceCoverage.sourceState
    {τ : Type u} (coverage : TransitionSourceCoverage τ)
    (transition : CheckedBeforeAfter) (source : coverage.source transition) :
    ∃ state, coverage.encode state = transition :=
  coverage.sourceComplete transition source

/- A transition domain must be bound to the concrete event's checked assignment
   relation before it can be an accepting API. The legacy singleton model is kept
   only for local evaluator fixtures. -/
def TypedTransitionModel.valid (_model : TypedTransitionModel)
    (_theory : EventB.Theory.Env) (_project : EventB.Typing.Project)
    (_obligation : Obligation) : Prop :=
  False

private def TypedTransitionModel.ofAssignment (fuel : Nat)
    (declarations : List (String × EventB.Typing.Ty)) (env : ValueEnv)
    (updates : List (String × EventB.Formula.Term)) : Option TypedTransitionModel :=
  match ValueEnv.parallelAssignTypedFuel fuel declarations env updates with
  | .error _ => none
  | .ok transition =>
      some
        { fuel := fuel
          wellFormed := fun candidate => candidate = transition
          inhabited := ⟨transition, rfl⟩
          supports := supportsBeforeAfterPredicate }

private def incrementTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 1)] }
    after := { values := [("x", .integer 2)] }
    declarations := [("x", .int)] }

private def incrementModel : TypedTransitionModel :=
  { fuel := 64
    wellFormed := fun transition => transition = incrementTransition
    inhabited := ⟨incrementTransition, rfl⟩
    supports := supportsBeforeAfterPredicate }

example : TypedTransitionModel.validUnchecked incrementModel
    { component := "M", name := "step/inv/INV", kind := "INV"
      hyps := [.bin "=" (.id "x") (.num 1)]
      goal := some (.bin "=" (.id "x'") (.num 2)) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro transition wellFormed
    subst transition
    have integerCompatible : (ValueType.integer == ValueType.integer) = true :=
      by native_decide
    have afterWellFormed : ValueEnv.valueIsWellFormed 63
        { values := [("x", .integer 2)] } (.integer 2) = true := by native_decide
    have beforeWellFormed : ValueEnv.valueIsWellFormed 63
        { values := [("x", .integer 1)] } (.integer 1) = true := by native_decide
    have beforeValidated : ValueEnv.validationOk 64 [("x", .int)]
        { values := [("x", .integer 1)] } = true := by native_decide
    have afterValidated : ValueEnv.validationOk 64 [("x", .int)]
        { values := [("x", .integer 2)] } = true := by native_decide
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        simp [incrementModel, TypedTransitionModel.denote, TypedTransitionModel.defined,
          evalBeforeAfter, evalPredicateFuel, evalValueFuel, EvalView.lookup, ValueEnv.lookup,
          Value.isWellFormed, ValueEnv.valueIsWellFormed, Value.sameType, Value.typeOf,
          ValueType.compatible, valueEqual,
          xPrimeEndsWith, xEndsWith, xPrimeBase,
          integerCompatible, afterWellFormed, beforeWellFormed, beforeValidated, afterValidated,
          Bind.bind, Except.bind,
          incrementTransition]
      · intro hypothesis member
        simp at member
        subst hypothesis
        refine ⟨true, ?_⟩
        simp [incrementModel, TypedTransitionModel.denote, TypedTransitionModel.defined,
          evalBeforeAfter, evalPredicateFuel, evalValueFuel, EvalView.lookup, ValueEnv.lookup,
          Value.isWellFormed, ValueEnv.valueIsWellFormed, Value.sameType, Value.typeOf,
          ValueType.compatible, valueEqual,
          xPrimeEndsWith, xEndsWith, xPrimeBase,
          integerCompatible, afterWellFormed, beforeWellFormed, beforeValidated, afterValidated,
          Bind.bind, Except.bind,
          incrementTransition]
    · intro _
      simp [incrementModel, TypedTransitionModel.denote, evalBeforeAfter, evalPredicateFuel,
        evalValueFuel, EvalView.lookup, ValueEnv.lookup, Value.isWellFormed,
        ValueEnv.valueIsWellFormed, Value.sameType,
        Value.typeOf, ValueType.compatible, valueEqual, xPrimeEndsWith, xEndsWith, xPrimeBase,
        integerCompatible, afterWellFormed, beforeWellFormed, beforeValidated, afterValidated,
        Bind.bind, Except.bind,
        incrementTransition]

example : ¬ TypedTransitionModel.validUnchecked incrementModel
    { component := "M", name := "forged/inv/INV", kind := "INV"
      goal := some (.bin "=" (.id "x'") (.num 3)) } := by
  intro proof
  have goalProof := (proof.2.2 incrementTransition rfl).2 (by simp)
  have integerCompatible : (ValueType.integer == ValueType.integer) = true :=
    by native_decide
  have afterWellFormed : ValueEnv.valueIsWellFormed 63
      { values := [("x", .integer 2)] } (.integer 2) = true := by native_decide
  have beforeValidated : ValueEnv.validationOk 64 [("x", .int)]
      { values := [("x", .integer 1)] } = true := by native_decide
  have afterValidated : ValueEnv.validationOk 64 [("x", .int)]
      { values := [("x", .integer 2)] } = true := by native_decide
  simp [incrementModel, TypedTransitionModel.denote, evalBeforeAfter, evalPredicateFuel,
    evalValueFuel, EvalView.lookup, ValueEnv.lookup, Value.isWellFormed,
    ValueEnv.valueIsWellFormed, Value.sameType,
    Value.typeOf, ValueType.compatible, valueEqual, xPrimeEndsWith, xEndsWith, xPrimeBase,
    integerCompatible, afterWellFormed, beforeValidated, afterValidated,
    Bind.bind, Except.bind,
    incrementTransition] at goalProof

#guard supportsPredicate (.bin "<" (.num 0) (.num 1))
#guard !supportsPredicate (.app (.id "f") (.num 0))
#guard match ValueEnv.parallelAssign { values := [("x", .integer 1), ("y", .integer 2)] }
    [("x", .id "y"), ("y", .id "x")] with
  | .ok transition =>
      transition.after.lookupMatches "x" (.integer 2) &&
      transition.after.lookupMatches "y" (.integer 1)
  | .error _ => false
#guard match ValueEnv.parallelAssign { values := [("x", .integer 1)] }
    [("x", .num 0), ("x", .num 1)] with
  | .error (.duplicateAssignment _) => true
  | _ => false
#guard match evalPredicate {} (.bin "∈" (.num 1) (.id "BOOL")) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalPredicate {} (.bin "=" (.set [.num 1, .num 2]) (.set [.num 2, .num 1])) with
  | .ok true => true
  | _ => false
#guard match evalPredicate { values := [("b", .boolean true)] }
    (.bin "=" (.set [.set [.num 1]]) (.set [.set [.id "b"]])) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalPredicate {} (.bin "∈" (.num 1) (.id "BOOL")) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalValue {} (.bin "+" (.num 1) (.id "BOOL")) with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match evalValue {} (.bin "÷" (.num 1) (.num 0)) with
  | .error .divisionByZero => true
  | _ => false
#guard match evalValue {} (.bin "," (.num 1) (.num 2)) with
  | .error (.unsupported _) => true
  | _ => false
#guard match evalValue {} (.id "missing") with
  | .error (.unbound "missing") => true
  | _ => false
#guard match evalValue {} (.id "x'") with
  | .error (.unsupported _) => true
  | _ => false
#guard match evalValue { values := [("s", .set [.integer 1, .boolean true])] } (.id "s") with
  | .error .invalidValue => true
  | _ => false
#guard match evalPredicate { values := [("s", .set [.integer 1, .boolean true])] }
    (.bin "∈" (.num 1) (.id "s")) with
  | .error .invalidValue => true
  | _ => false
#guard match ValueEnv.parallelAssignTerms {} ["x"] [] with
  | .error .assignmentArity => true
  | _ => false
#guard match ValueEnv.validate [("x", .int)] { values := [("x", .integer 1)] } with
  | .ok () => true
  | _ => false
#guard match ValueEnv.validate [("x", .int)] { values := [("x", .boolean true)] } with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match ValueEnv.parallelAssignTyped
    [("x", .int), ("y", .int)]
    { values := [("x", .integer 1), ("y", .integer 2)] }
    [("x", .id "y"), ("y", .id "x")] with
  | .ok transition =>
      transition.after.lookupMatches "x" (.integer 2) &&
      transition.after.lookupMatches "y" (.integer 1)
  | _ => false
#guard match ValueEnv.parallelAssignTyped
    [("x", .int), ("b", .bool)]
    { values := [("x", .integer 1), ("b", .boolean true)] }
    [("x", .id "b")] with
  | .error (.typeMismatch _ _) => true
  | _ => false
#guard match ValueEnv.validate [("a", .given "AIR")] {
    values := [("a", .atom "AIR" "one")], carriers := [("AIR", ["one"])] } with
  | .ok () => true
  | _ => false
#guard match ValueEnv.validate [("a", .given "AIR")] {
    values := [("a", .atom "AIR" "one")] } with
  | .error .invalidValue => true
  | _ => false
#guard match CheckedBeforeAfter.make 32 [("x", .int)]
    { values := [("x", .integer 1)] } { values := [("x", .integer 2)] } with
  | .ok transition =>
      match evalBeforeAfter 32 transition (.bin "=" (.id "x'") (.num 2)) with
      | .ok true => true
      | _ => false
  | _ => false
#guard match CheckedBeforeAfter.make 32 [("x", .int)]
    { values := [("x", .integer 1)] } { values := [("y", .integer 2)] } with
  | .error (.unbound "x") => true
  | _ => false
#guard match CheckedBeforeAfter.make 32 [("x", .int)]
    { values := [("x", .integer 1)] } { values := [("x", .integer 2)] } with
  | .ok transition =>
      match evalBeforeAfter 32 transition (.bin "=" (.id "y'") (.num 2)) with
      | .error (.unbound "y'") => true
      | _ => false
  | _ => false
#guard supportsBeforeAfterPredicate
  (.bin "∧" (.bin "=" (.id "x") (.num 1)) (.bin "=" (.id "x'") (.num 2)))
#guard match evalPredicateWithFuel 0 {} (.id "⊤") with
  | .error .fuelExhausted => true
  | _ => false

private def typedFormulaModel (supports : EventB.Formula.Term → Bool) : TypedFormulaModel :=
  { declarations := [("x", .int)]
    fuel := 128
    wellFormed := fun env => ValueEnv.validationOk 128 [("x", .int)] env = true
    inhabited := ⟨{ values := [("x", .integer 0)] }, by native_decide⟩
    validated := fun _ proof => proof
    complete := fun _ proof => proof
    supports := supports }

private def typedEnv : ValueEnv := { values := [("x", .integer 0)] }

private theorem typedEnvWellFormed (supports : EventB.Formula.Term → Bool) :
    (typedFormulaModel supports).wellFormed typedEnv := by
  change ValueEnv.validationOk 128 [("x", .int)] typedEnv = true
  native_decide

private theorem typedFormulaValid :
    TypedFormulaModel.validUnchecked (typedFormulaModel (fun _ => true))
    { component := "M", name := "arith/THM", kind := "THM"
      hyps := [.bin "≤" (.num 0) (.num 1)]
      goal := some (.bin "<" (.num 0) (.num 1)) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro env _
    have integerCompatible : (ValueType.integer == ValueType.integer) = true := by native_decide
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        simp [typedFormulaModel, evalPredicate, evalPredicateAtFuel, evalPredicateWithFuel,
          evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel, Bind.bind, Except.bind]
      · intro hypothesis member
        simp at member
        subst hypothesis
        refine ⟨true, ?_⟩
        simp [typedFormulaModel, evalPredicate, evalPredicateAtFuel, evalPredicateWithFuel,
          evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel, Bind.bind, Except.bind]
    · intro _
      simp [typedFormulaModel, TypedFormulaModel.denote, evalPredicate, evalPredicateAtFuel,
        evalPredicateWithFuel, evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel,
        Bind.bind, Except.bind]

def constantTypedFormulaModel : TypedFormulaModel :=
  { declarations := []
    fuel := 128
    wellFormed := fun env => ValueEnv.validationOk 128 [] env = true
    inhabited := ⟨{}, by native_decide⟩
    validated := fun _ proof => proof
    complete := fun _ proof => proof
    supports := fun _ => true }

theorem constantTypedFormulaModel_taut_valid :
    TypedFormulaModel.validUnchecked constantTypedFormulaModel
      { component := "M", name := "taut/THM", kind := "THM"
        goal := some (.bin "=" (.num 1) (.num 1)) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro env _
    have integerCompatible : (ValueType.integer == ValueType.integer) = true := by native_decide
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        simp [constantTypedFormulaModel, TypedFormulaModel.defined,
          evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel, evalValue,
          evalValueWithFuel, evalValueFuel, ValueEnv.lookup, Value.sameType,
          Value.typeOf, ValueType.compatible, valueEqual, integerCompatible,
          Bind.bind, Except.bind]
      · intro hypothesis member
        simp at member
    · intro _
      simp [constantTypedFormulaModel, TypedFormulaModel.denote,
        evalPredicateAtFuel, evalPredicateWithFuel, evalPredicateFuel, evalValue,
        evalValueWithFuel, evalValueFuel, ValueEnv.lookup, Value.sameType,
        Value.typeOf, ValueType.compatible, valueEqual, integerCompatible,
        Bind.bind, Except.bind]

private def constantTransition : CheckedBeforeAfter :=
  { before := {}, after := {}, declarations := [] }

def constantTypedTransitionModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := fun transition => transition = constantTransition
    inhabited := ⟨constantTransition, rfl⟩
    supports := fun _ => true }

theorem constantTypedTransitionModel_taut_valid :
    TypedTransitionModel.validUnchecked constantTypedTransitionModel
      { component := "M", name := "INITIALISATION/taut/INV", kind := "INV"
        goal := some (.bin "=" (.num 1) (.num 1)) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro transition transitionValid
    subst transition
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        have validation : ValueEnv.validationOk 128 [] ({} : ValueEnv) = true := by
          native_decide
        have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
          native_decide
        simp [constantTypedTransitionModel, TypedTransitionModel.defined, constantTransition,
          validation, integerCompatible, evalBeforeAfter, evalPredicateFuel,
          evalValueFuel, ValueEnv.lookup,
          Value.sameType, Value.typeOf, ValueType.compatible, valueEqual,
          Bind.bind, Except.bind]
      · intro hypothesis member
        simp at member
    · intro _
      have beforeValidation : ValueEnv.validationOk 128 [] ({} : ValueEnv) = true := by
        native_decide
      have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
        native_decide
      simp [TypedTransitionModel.denote, constantTypedTransitionModel, constantTransition,
        beforeValidation, integerCompatible, evalBeforeAfter, evalPredicateFuel,
        evalValueFuel, ValueEnv.lookup, Value.sameType, Value.typeOf, ValueType.compatible,
        valueEqual, Bind.bind, Except.bind]

theorem constantTypedTransitionModel_grd_taut_valid :
    TypedTransitionModel.validUnchecked constantTypedTransitionModel
      { component := "C", name := "step/g/GRD", kind := "GRD"
        goal := some (.bin "=" (.num 1) (.num 1)) } := by
  simpa [TypedTransitionModel.validUnchecked, Obligation.semanticShapeValid, Obligation.shapeValid,
    Obligation.transitionValuationSupported, POClass.ofKind,
    POClass.transitionValuationSupported] using constantTypedTransitionModel_taut_valid

theorem typedTransitionModel_taut_validOnDomain
    (model : TypedTransitionModel)
    (domain : CheckedBeforeAfter → Prop)
    (domainValid : ∀ transition, domain transition →
      ValueEnv.validationOk 128 transition.declarations transition.before = true ∧
      ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (obligation : Obligation)
    (shape : obligation.semanticShapeValid = true)
    (valuation : obligation.transitionValuationSupported = true)
    (goal : obligation.goal = some (.bin "=" (.num 1) (.num 1)))
    (hyps : obligation.hyps = [])
    (fuel : model.fuel = 128)
    (supports : ∀ term, model.supports term = true) :
    TypedTransitionModel.validOnDomain model domain obligation := by
  have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
    native_decide
  unfold TypedTransitionModel.validOnDomain
  have goalSupported : model.supports (.bin "=" (.num 1) (.num 1)) = true :=
    supports _
  simp [shape, valuation, goal, hyps, fuel, goalSupported,
    TypedTransitionModel.defined, TypedTransitionModel.denote, evalBeforeAfter,
    evalPredicateFuel, evalValueFuel, ValueEnv.lookup, Value.sameType,
    Value.typeOf, ValueType.compatible, valueEqual, integerCompatible,
    Bind.bind, Except.bind]
  intro transition transitionDomain
  obtain ⟨beforeValid, afterValid⟩ := domainValid transition transitionDomain
  simp [beforeValid, afterValid, evalPredicateFuel, evalValueFuel,
    ValueEnv.lookup, Value.sameType, Value.typeOf, ValueType.compatible,
    valueEqual, integerCompatible, Bind.bind, Except.bind]

theorem typedTransitionModel_closed_validOnDomain
    (model : TypedTransitionModel)
    (domain : CheckedBeforeAfter → Prop)
    (domainValid : ∀ transition, domain transition →
      ValueEnv.validationOk 128 transition.declarations transition.before = true ∧
      ValueEnv.validationOk 128 transition.declarations transition.after = true)
    (obligation : Obligation)
    (shape : obligation.semanticShapeValid = true)
    (valuation : obligation.transitionValuationSupported = true)
    (goal : EventB.Formula.Term)
    (goalExact : obligation.goal = some goal)
    (hyps : obligation.hyps = [])
    (fuel : model.fuel = 128)
    (supports : model.supports goal = true)
    (evaluation : ∀ transition, domain transition →
      evalBeforeAfter 128 transition goal = .ok true) :
    TypedTransitionModel.validOnDomain model domain obligation := by
  unfold TypedTransitionModel.validOnDomain
  simp [shape, valuation, goalExact, hyps, fuel, supports,
    TypedTransitionModel.validOnDomain]
  intro transition transitionDomain
  have evaluated := evaluation transition transitionDomain
  constructor
  · refine ⟨true, ?_⟩
    rw [fuel]
    exact evaluated
  · change evalBeforeAfter model.fuel transition goal = .ok true
    rw [fuel]
    exact evaluated

private def stutterTransition : CheckedBeforeAfter :=
  { before := { values := [("x", .integer 0)] }
    after := { values := [("x", .integer 0)] }
    declarations := [("x", .int)] }

def stutterTypedTransitionModel : TypedTransitionModel :=
  { fuel := 128
    wellFormed := fun transition => transition = stutterTransition
    inhabited := ⟨stutterTransition, rfl⟩
    supports := supportsBeforeAfterPredicate }

theorem stutterTypedTransitionModel_sim_valid :
    TypedTransitionModel.validUnchecked stutterTypedTransitionModel
      { component := "C", name := "step/set/SIM", kind := "SIM"
        hyps := [.bin "∈" (.id "x") (.id "ℤ"),
          .bin "∈" (.id "x") (.id "ℤ")]
        goal := some (.bin "=" (.id "x") (.id "x")) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro transition transitionValid
    subst transition
    have integerCompatible : (ValueType.integer == ValueType.integer) = true := by
      native_decide
    have beforeWellFormed : ValueEnv.valueIsWellFormed 127
        { values := [("x", .integer 0)] } (.integer 0) = true := by
      native_decide
    have afterWellFormed : ValueEnv.valueIsWellFormed 127
        { values := [("x", .integer 0)] } (.integer 0) = true := by
      native_decide
    have beforeValidated : ValueEnv.validationOk 128 [("x", .int)]
        { values := [("x", .integer 0)] } = true := by
      native_decide
    have afterValidated : ValueEnv.validationOk 128 [("x", .int)]
        { values := [("x", .integer 0)] } = true := by
      native_decide
    have xEndsWith : "x".endsWith "'" = false := by
      native_decide
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        simp [stutterTypedTransitionModel, TypedTransitionModel.defined,
          stutterTransition, evalBeforeAfter, evalPredicateFuel, evalValueFuel,
          evalValueListFuel, Value.makeSet,
          EvalView.lookup, ValueEnv.lookup, Value.isWellFormed,
          ValueEnv.valueIsWellFormed, Value.sameType, Value.typeOf,
          ValueType.compatible, Value.contains, memberOf, subsetOf, valueEqual,
          xEndsWith, beforeWellFormed, afterWellFormed,
          beforeValidated, afterValidated, integerCompatible,
          Bind.bind, Except.bind]
      · intro hypothesis member
        simp at member
        subst hypothesis
        refine ⟨true, ?_⟩
        simp [stutterTypedTransitionModel, TypedTransitionModel.defined,
          stutterTransition, evalBeforeAfter, evalPredicateFuel, evalValueFuel,
          EvalView.lookup, ValueEnv.lookup, Value.isWellFormed,
          ValueEnv.valueIsWellFormed, Value.sameType, Value.typeOf,
          ValueType.compatible, Value.contains, memberOf, subsetOf, valueEqual,
          xEndsWith, beforeWellFormed, afterWellFormed,
          beforeValidated, afterValidated, integerCompatible,
          Bind.bind, Except.bind]
    · intro _
      simp [TypedTransitionModel.denote, stutterTypedTransitionModel,
        stutterTransition, evalBeforeAfter, evalPredicateFuel, evalValueFuel,
        evalValueListFuel, Value.makeSet,
        EvalView.lookup, ValueEnv.lookup, Value.isWellFormed,
        ValueEnv.valueIsWellFormed, Value.sameType, Value.typeOf,
        ValueType.compatible, Value.contains, memberOf, subsetOf, valueEqual,
        xEndsWith, beforeWellFormed, afterWellFormed,
        beforeValidated, afterValidated, integerCompatible,
        Bind.bind, Except.bind]

theorem stutterTypedTransitionModel_fis_choose_valid :
    TypedTransitionModel.validUnchecked stutterTypedTransitionModel
      { component := "M", name := "INITIALISATION/choose/FIS", kind := "FIS"
        goal := some (.bin "≠" (.set [.num 0]) (.set [])) } := by
  constructor
  · rfl
  constructor
  · rfl
  · intro transition transitionValid
    subst transition
    have beforeWellFormed : ValueEnv.valueIsWellFormed 127
        { values := [("x", .integer 0)] } (.integer 0) = true := by
      native_decide
    have afterWellFormed : ValueEnv.valueIsWellFormed 127
        { values := [("x", .integer 0)] } (.integer 0) = true := by
      native_decide
    have beforeValidated : ValueEnv.validationOk 128 [("x", .int)]
        { values := [("x", .integer 0)] } = true := by
      native_decide
    have afterValidated : ValueEnv.validationOk 128 [("x", .int)]
        { values := [("x", .integer 0)] } = true := by
      native_decide
    constructor
    · constructor
      · refine ⟨true, ?_⟩
        native_decide
      · intro _
        simp
    · intro _
      change evalBeforeAfter 128 stutterTransition
        (.bin "≠" (.set [.num 0]) (.set [])) = .ok true
      native_decide

example : FormulaModel.validUnchecked
    ((typedFormulaModel (fun _ => true)).on (fun (_ : Unit) => typedEnv))
    { component := "M", name := "arith/THM", kind := "THM"
      hyps := [.bin "≤" (.num 0) (.num 1)]
      goal := some (.bin "<" (.num 0) (.num 1)) } := by
  apply TypedFormulaModel.valid_on
  · exact typedFormulaValid
  · intro _
    exact typedEnvWellFormed _

example : ¬ TypedFormulaModel.validUnchecked (typedFormulaModel supportsPredicate)
    { component := "M", name := "false/THM", kind := "THM",
      goal := some (.bin "<" (.num 1) (.num 0)) } := by
  intro proof
  have goalProof := (proof.2.2 typedEnv (typedEnvWellFormed _)).2 (by simp)
  simp [typedFormulaModel, TypedFormulaModel.denote, evalPredicate, evalPredicateAtFuel,
    evalPredicateWithFuel, evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel,
    Bind.bind, Except.bind] at goalProof

example : ¬ TypedFormulaModel.validUnchecked (typedFormulaModel supportsPredicate)
    { component := "M", name := "unsupported/THM", kind := "THM"
      goal := some (.app (.id "f") (.num 0)) } := by
  simp [TypedFormulaModel.validUnchecked, typedFormulaModel, supportsPredicate]

/- An ill-typed hypothesis is an evaluator error, not a false premise that can
   vacuously discharge a false goal. -/
example : ¬ TypedFormulaModel.validUnchecked (typedFormulaModel (fun _ => true))
    { component := "M", name := "illTyped/THM", kind := "THM"
      hyps := [.bin "∈" (.num 1) (.id "BOOL")]
      goal := some (.id "⊥") } := by
  intro proof
  have defined := (proof.2.2 typedEnv (typedEnvWellFormed _)).1.2
    (.bin "∈" (.num 1) (.id "BOOL")) (by simp)
  rcases defined with ⟨value, evaluated⟩
  simp [typedFormulaModel, evalPredicate, evalPredicateAtFuel, evalPredicateWithFuel,
    evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel, Bind.bind, Except.bind,
    Value.contains] at evaluated

example : TypedFormulaModel.validUnchecked (typedFormulaModel (fun _ => true))
    { component := "M", name := "defined/WWD", kind := "WWD"
      hyps := [.bin "∈" (.num 0) (.id "ℤ")] } := by
  constructor
  · rfl
  · intro env _ hypothesis member
    have : hypothesis = .bin "∈" (.num 0) (.id "ℤ") := by simpa using member
    subst hypothesis
    constructor
    · refine ⟨true, ?_⟩
      simp [typedFormulaModel, evalPredicate, evalPredicateAtFuel, evalPredicateWithFuel,
        evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel, Bind.bind, Except.bind,
        Value.contains]
    · simp [typedFormulaModel, TypedFormulaModel.denote, evalPredicate, evalPredicateAtFuel,
        evalPredicateWithFuel, evalPredicateFuel, evalValue, evalValueWithFuel, evalValueFuel,
        Bind.bind, Except.bind, Value.contains]

example : ¬ TypedFormulaModel.validUnchecked (typedFormulaModel supportsPredicate)
    { component := "M", name := "unsupported/WWD", kind := "WWD"
      hyps := [.app (.id "f") (.num 0)] } := by
  simp [TypedFormulaModel.validUnchecked, typedFormulaModel, supportsPredicate]

/- Negative control: a missing goal is never silently treated as a valid sequent. -/
example : ¬ FormulaModel.validUnchecked
    ({ denote := fun _ _ => True } : FormulaModel Unit)
    { name := "missing/INV", kind := "INV" } := by
  simp [FormulaModel.validUnchecked]

/- Positive control: a caller-provided interpretation can discharge an obligation. -/
example : FormulaModel.validUnchecked
    ({ denote := fun _ _ => True } : FormulaModel Unit)
    { name := "true/THM", kind := "THM", goal := some (.id "⊤") } := by
  simp [FormulaModel.validUnchecked, validSequent]

end EventB.POG
