/-
Proof obligation generation.

The gate is the set of PO names Rodin recorded in each `.bpo`. Names are not cosmetic:
`Hold_Button/inv4,1/INV` says exactly which event must preserve which invariant, so
reproducing the set means reproducing Rodin's filtering rules, which decide when an
obligation is needed at all. Generating too many is as wrong as generating too few.

The classes, with their share of the 1133 obligations in the corpus:

  INV  934  event preserves invariant
  WD    93  a predicate is well defined
  GRD   61  a refined event's guards imply the abstract ones
  SIM   23  a refined event's actions simulate the abstract ones
  THM   13  an invariant or axiom marked `theorem` follows from what precedes it
  WFIS   8  a witness is feasible
  WWD    1  a witness is well defined
-/

import EventB.Typing.Check

namespace EventB.POG

open EventB EventB.Formula EventB.Typing EventB.Prelude

/-- A generated obligation. `goal` is `none` for the classes whose statement is not
derived yet, so the name gate keeps working while the statement gate grows. -/
structure Obligation where
  component : String := ""
  name : String
  kind : String
  theoryRoots : List String := []
  goal : Option Term := none
  /-- Everything the goal may assume, in Rodin's order. -/
  hyps : List Term := []
  /-- Typechecking and model-resolution errors discovered before generation. -/
  diagnostics : List String := []
  deriving BEq, Repr, Inhabited, DecidableEq

/-- The only checked obligation without a translated statement is witness WD: Rodin
records its definedness formula as a hypothesis of the sequent. Every other checked
obligation must carry exactly one goal. -/
def Obligation.shapeValid (obligation : Obligation) : Bool :=
  match obligation.kind, obligation.goal with
  | "WWD", none => !obligation.hyps.isEmpty
  | "WWD", some _ => false
  | _, some _ => true
  | _, none => false

#guard ({ name := "w/WWD", kind := "WWD", hyps := [.id "defined"] } : Obligation).shapeValid
#guard !({ name := "i/INV", kind := "INV" } : Obligation).shapeValid

def formulaLanguageVersion : String := "eventb-formula-v2"

private def canonicalField (value : String) : String :=
  s!"{value.length}:{value}"

private def canonicalList (values : List String) : String :=
  s!"{values.length}[{String.intercalate "" (values.map canonicalField)}]"

def Obligation.canonical (obligation : Obligation) : String :=
  String.intercalate "\n"
    ["scope=" ++ canonicalField obligation.component
    , "obligation=" ++ canonicalField obligation.name
    , "kind=" ++ canonicalField obligation.kind
    , "formula-language=" ++ canonicalField formulaLanguageVersion
    , "theories=" ++ canonicalList obligation.theoryRoots
    , "diagnostics=" ++ canonicalList obligation.diagnostics
    , "hyps=" ++ canonicalList (obligation.hyps.map Formula.print)
    , "goal=" ++ canonicalField (obligation.goal.map Formula.print |>.getD "<pending>")]

private def childrenOf (e : Elem) (tag : String) : List Elem :=
  e.children.filter (fun c => c.tag == "org.eventb.core." ++ tag)

private def attrOf (e : Elem) (key : String) : Option String :=
  e.attr? ("org.eventb.core." ++ key)

private def labelOf (e : Elem) : String := (attrOf e "label").getD ""

private def targetName (e : Elem) : Option String :=
  (attrOf e "target").map (fun t => (t.splitOn "/").getLast!)

private def eventTargets (ev : Elem) : List String :=
  if labelOf ev == "INITIALISATION" then ["INITIALISATION"]
  else (childrenOf ev "refinesEvent").filterMap targetName

/-- Exact abstract events named by a concrete event's `refinesEvent` children. -/
def eventRefinementTargets (p : Project) (machine event : String) : List String :=
  match lookupComponent p machine with
  | none => []
  | some component =>
      match (childrenOf component.elem "event").find?
          (fun candidate => labelOf candidate == event) with
      | none => []
      | some current => eventTargets current

/- Keep the source machine together with each refined-event label.  The older
   `eventRefinementTargets` API remains the compatibility label projection; checked
   refinement adapters use this locator-preserving view. -/
def eventRefinementTargetLocators (p : Project) (machine event : String) :
    List (String × String) :=
  match lookupComponent p machine with
  | none => []
  | some component =>
      let abstractMachine :=
        (childrenOf component.elem "refinesMachine").filterMap targetName |>.head?.getD ""
      match (childrenOf component.elem "event").find?
          (fun candidate => labelOf candidate == event) with
      | none => []
      | some current =>
          (childrenOf current "refinesEvent").filterMap fun target =>
            (attrOf target "target").map fun raw =>
              let parts := raw.splitOn "/"
              let targetEvent := parts.getLast!
              let targetMachine :=
                if parts.length > 1 then parts.dropLast.getLast!
                else abstractMachine
              (targetMachine, targetEvent)

/-- Exact convergence attribute of a source event.  Semantic adapters use this
    instead of inferring anticipated/convergent semantics from a VAR name. -/
def eventConvergenceMode? (p : Project) (machine event : String) : Option String :=
  match lookupComponent p machine with
  | none => none
  | some component =>
      (childrenOf component.elem "event").find?
        (fun candidate => labelOf candidate == event) |>.bind (attrOf · "convergence")

private def isExtended (ev : Elem) : Bool :=
  (attrOf ev "extended").getD "false" == "true" ||
    (childrenOf ev "refinesEvent").any
      (fun reference => (attrOf reference "extended").getD "false" == "true")

/-- Identifiers occurring in a formula. -/
def identifiers : Term → List String
  | .id n => [n]
  | .num _ => []
  | .bin _ a b => identifiers a ++ identifiers b
  | .pre _ a | .post _ a => identifiers a
  | .app f a => identifiers f ++ identifiers a
  | .img r a => identifiers r ++ identifiers a
  | .set ts => ts.flatMap identifiers
  | .bind _ p b => identifiers p ++ identifiers b

private def freeIdentifiers (bound : List String) : Term → List String
  | .id n => if bound.contains n then [] else [n]
  | .num _ => []
  | .bin _ a b => freeIdentifiers bound a ++ freeIdentifiers bound b
  | .pre _ a | .post _ a => freeIdentifiers bound a
  | .app f a => freeIdentifiers bound f ++ freeIdentifiers bound a
  | .img r a => freeIdentifiers bound r ++ freeIdentifiers bound a
  | .set ts => ts.flatMap (freeIdentifiers bound)
  | .bind _ pattern body =>
      freeIdentifiers bound pattern ++
        freeIdentifiers (patternNames pattern ++ bound) body

private def freeOf (formula : String) : List String :=
  match Formula.parse formula with
  | .ok t => freeIdentifiers [] t
  | .error _ => []

/-- The substitution an action performs. Only the deterministic form `v ≔ E` yields
one: `v :∈ S` and `v :∣ P` choose a value, which Rodin states with a fresh variable
rather than a replacement, and which this does not derive yet. -/
private def substOf (action : Elem) : List (String × Term) :=
  match attrOf action "assignment" with
  | none => []
  | some a =>
    match Formula.parse a with
    -- `f(x) ≔ E` overrides the function at one point. Rodin writes the result as
    -- `f{x ↦ E}`, so the substitution builds exactly that.
    | .ok (.bin "≔" lhs rhs) =>
        let update : Term → Term → Option (String × Term)
          | .id v, e => some (v, e)
          | .app (.id f) x, e =>
              some (f, .bin "" (.id f) (.set [.bin "↦" x e]))
          | _, _ => none
        (Formula.flattenCommas lhs).zip (Formula.flattenCommas rhs)
          |>.filterMap (fun (v, e) => update v e)
    | _ => []

private def witnessBinding (witness : Elem) : Option (String × Term) :=
  match Formula.parse ((attrOf witness "predicate").getD "") with
  | .ok (.bin "=" left right) =>
      match attrOf witness "label" with
      | some label =>
          if left == .id label then some (label, right)
          else if right == .id label then some (label, left)
          else match left with
            | .id v => some (v, right)
            | _ => match right with
              | .id v => some (v, left)
              | _ => none
      | none =>
          match left with
          | .id v => some (v, right)
          | _ => match right with
            | .id v => some (v, left)
            | _ => none
  | _ => none

private def witnessVariable (witness : Elem) : Option String :=
  (witnessBinding witness).map (·.1) <|> attrOf witness "label"

private def witnessSubstitution (witness : Elem) : Option (String × Term) :=
  match Formula.parse ((attrOf witness "predicate").getD "") with
  | .ok (.bin "=" (.id v) e) => some (v, e)
  | _ => none

/-- The variables an action assigns. Rodin's three assignment forms all name their
targets on the left: `v ≔ E`, `v :∈ S`, and `v, w :∣ P`. -/
private def assignedBy (action : Elem) : List String :=
  match attrOf action "assignment" with
  | none => []
  | some a =>
    match Formula.parse a with
    | .error _ => []
    | .ok (.bin op lhs _) =>
        if op == "≔" then (substOf action).map (·.1)
        else if op == ":∈" || op == ":∣" then
          Formula.flattenCommas lhs |>.filterMap fun term =>
            match term with
            | .id n => some n
            | .app (.id f) _ => some f
            | _ => none
        else []
    | .ok _ => []

private def targetEventName (ev : Elem) : String :=
  (eventTargets ev).head?.getD ""

private def beforeElem (target : Elem) : List Elem → List Elem
  | [] => []
  | elem :: elems => if elem == target then [] else elem :: beforeElem target elems

/-- An event marked `extended` inherits the parameters, guards and actions of the event
it refines, so its effective children are its own plus everything up the chain.

`depth` bounds the walk by the number of components: a refinement chain longer than that
has revisited a machine, which means the model has a `refines` cycle and no fixed point
exists. Well-formed projects never reach the bound, and reaching it returns what has
been gathered so far rather than looping. -/
def inheritedChildren (p : Project) (tag : String) : Nat → String → Elem → List Elem
  | 0, _, ev => childrenOf ev tag
  | depth + 1, machine, ev =>
    let own := childrenOf ev tag
    if !isExtended ev then own else
      match lookupComponent p machine with
      | none => own
      | some m =>
        let abstract := (childrenOf m.elem "refinesMachine").filterMap targetName
        let inherited := abstract.flatMap fun am =>
          match lookupComponent p am with
          | none => []
          | some a =>
            eventTargets ev |>.flatMap fun target =>
              match (childrenOf a.elem "event").find? (fun e => labelOf e == target) with
              | none => []
              | some ae => inheritedChildren p tag depth am ae
        inherited ++ own

def effectiveActions (p : Project) (machine : String) (ev : Elem) : List Elem :=
  inheritedChildren p "action" p.length machine ev

def effectiveGuards (p : Project) (machine : String) (ev : Elem) : List Elem :=
  inheritedChildren p "guard" p.length machine ev

private def parseGuardPredicates? : List Elem → Option (List Term)
  | [] => some []
  | guard :: guards => do
      let source ← guard.attr? "org.eventb.core.predicate"
      let predicate ← (Formula.parse source).toOption
      let rest ← parseGuardPredicates? guards
      pure (predicate :: rest)

/-- Exact parsed guard predicates of an event, including inherited guards.  A missing
    event or malformed guard is rejected instead of being converted to an empty list. -/
def eventGuardPredicates (p : Project) (machine event : String) : Option (List Term) :=
  match lookupComponent p machine with
  | none => none
  | some component =>
      match (childrenOf component.elem "event").find?
          (fun candidate => labelOf candidate == event) with
      | none => none
      | some current => parseGuardPredicates? (effectiveGuards p machine current)

/-- The substitution an event performs, including what the abstract machine still does
to variables the concrete event does not touch.

A gluing invariant mentions abstract variables, and those keep evolving under the
abstract event even when the refinement never names them, so `scheduledAirplanes =
dom(landing_sequence)` becomes `∅ = dom(∅)` under an INITIALISATION that only assigns
`landing_sequence` here and leaves the other to the machine above. Concrete assignments
win; `depth` bounds the walk by the component count, as elsewhere. -/
private def eventActions (p : Project) : Nat → String → Elem → List Elem
  | 0, machine, ev =>
      match lookupComponent p machine with
      | some component => initializationActions p component ev
      | none => childrenOf ev "action"
  | depth + 1, machine, ev =>
    let own := match lookupComponent p machine with
      | some component => initializationActions p component ev
      | none => childrenOf ev "action"
    let inherited :=
      match lookupComponent p machine with
      | none => []
      | some m =>
          ((childrenOf m.elem "refinesMachine").filterMap targetName).flatMap fun am =>
            match lookupComponent p am with
            | none => []
            | some a =>
                eventTargets ev |>.flatMap fun target =>
                  match (childrenOf a.elem "event").find? (fun e => labelOf e == target) with
                  | none => []
                  | some ae => eventActions p depth am ae
    own ++ inherited.filter (fun q =>
      !(assignedBy q).any (fun v => own.any (fun o => (assignedBy o).contains v)))

private def transitionActions (p : Project) (machine : String) (ev : Elem) : List Elem :=
  eventActions p p.length machine ev

private def accurateTransitionActions (p : Project) (machine : String) (ev : Elem) : List Elem :=
  match lookupComponent p machine with
  | none => childrenOf ev "action"
  | some component =>
      if labelOf ev == "INITIALISATION" then initializationActions p component ev
      else effectiveActions p machine ev

private def refinementTransitionActions (p : Project) (machine : String) (ev : Elem) : List Elem :=
  accurateTransitionActions p machine ev

def eventSubst (p : Project) : Nat → String → Elem → List (String × Term)
  | 0, machine, ev =>
      (transitionActions p machine ev).flatMap substOf
  | _, machine, ev => (transitionActions p machine ev).flatMap substOf

private def actionRelation (action : Elem) : Option Term :=
  match attrOf action "assignment" with
  | none => none
  | some source =>
      match Formula.parse source with
      | .ok (.bin ":∈" lhs set) =>
          let relations := Formula.flattenCommas lhs |>.filterMap fun term =>
            match term with
            | .id v => some (.bin "∈" (.id (v ++ "'")) set)
            | _ => none
          match relations with
          | [] => none
          | relation :: rest =>
              some (rest.foldl (fun acc next => .bin "∧" acc next) relation)
      | .ok (.bin ":∣" _ predicate) => some predicate
      | _ => none

private def actionRelationAccurate (action : Elem) : Option Term :=
  match attrOf action "assignment" with
  | none => none
  | some source =>
      match Formula.parse source with
      | .ok (.bin ":∈" lhs set) =>
          let targets := Formula.flattenCommas lhs |>.filterMap fun term =>
            match term with
            | .id v => some (.id (v ++ "'"))
            | _ => none
          match targets with
          | [] => none
          | [target] => some (.bin "∈" target set)
          | target :: rest =>
              let tuple := rest.foldl (fun acc next => .bin "↦" acc next) target
              some (.bin "∈" tuple set)
      | .ok (.bin ":∣" _ predicate) => some predicate
      | _ => none

private def nondeterministicSubst (action : Elem) : List (String × Term) :=
  match attrOf action "assignment" with
  | some source =>
      match Formula.parse source with
      | .ok (.bin op _ _) =>
          if op == ":∈" || op == ":∣" then
            assignedBy action |>.map fun v => (v, .id (v ++ "'"))
          else []
      | _ => []
  | none => []

private def firstAssignments (pairs : List (String × Term)) : List (String × Term) :=
  pairs.foldl (fun acc pair =>
    if acc.any (fun prior => prior.1 == pair.1) then acc else acc ++ [pair]) []

private def eventStateSubst (p : Project) (name : String) (ev : Elem) : List (String × Term) :=
  firstAssignments ((transitionActions p name ev).flatMap fun action =>
    substOf action ++ nondeterministicSubst action)

private def eventRelationalHyps (p : Project) (name : String) (ev : Elem) : List Term :=
  (transitionActions p name ev).filterMap actionRelation

private def eventStateSubstMode (strict : Bool) (p : Project) (name : String)
    (ev : Elem) : List (String × Term) :=
  if strict then
    firstAssignments ((refinementTransitionActions p name ev).flatMap fun action =>
      substOf action ++ nondeterministicSubst action)
  else eventStateSubst p name ev

private def eventRelationalHypsMode (strict : Bool) (p : Project) (name : String)
    (ev : Elem) : List Term :=
  if strict then (refinementTransitionActions p name ev).filterMap actionRelationAccurate
  else eventRelationalHyps p name ev

private def deterministicAfterRelation (action : Elem) : List Term :=
  (substOf action).map fun (v, rhs) => .bin "=" (.id (v ++ "'")) rhs

private def actionAfterRelation (action : Elem) : List Term :=
  deterministicAfterRelation action ++ (actionRelation action).toList

private def actionAfterRelationAccurate (action : Elem) : List Term :=
  deterministicAfterRelation action ++ (actionRelationAccurate action).toList

private def frameRelations (variables : List String) (actions : List Elem) : List Term :=
  let assigned := actions.flatMap assignedBy
  (variables.filter (fun v => !assigned.contains v)).map fun v =>
    .bin "=" (.id (v ++ "'")) (.id v)

private def concreteStateRelations (variables : List String) (actions : List Elem) : List Term :=
  actions.flatMap actionAfterRelation ++ frameRelations variables actions

private def concreteStateRelationsAccurate (initialization : Bool) (variables : List String)
    (actions : List Elem) : List Term :=
  actions.flatMap actionAfterRelationAccurate ++
    if initialization then [] else frameRelations variables actions

private def concreteStateRelationsMode (strict initialization : Bool) (variables : List String)
    (actions : List Elem) : List Term :=
  if strict then concreteStateRelationsAccurate initialization variables actions
  else concreteStateRelations variables actions

/-- Exact after-state relations selected by the strict transition path.  This is
    public so source-bound semantic adapters can consume the same action slice as
    strict POG generation, including nondeterministic assignments and frames. -/
def eventStateRelations (p : Project) (machine event : String)
    (variables : List String) : List Term :=
  match lookupComponent p machine with
  | none => []
  | some component =>
      match (childrenOf component.elem "event").find?
          (fun candidate => labelOf candidate == event) with
      | none => []
      | some current =>
          let actions := if event == "INITIALISATION" then
              EventB.Typing.initializationActions p component current
            else effectiveActions p machine current
          actions.flatMap actionAfterRelationAccurate ++
            if event == "INITIALISATION" then [] else frameRelations variables actions

private def actionAfterSubst (action : Elem) : List (String × Term) :=
  ((substOf action).map fun (v, rhs) => (v ++ "'", rhs)) ++
    ((nondeterministicSubst action).map fun (v, rhs) => (v ++ "'", rhs))

/-- Guards and actions of the abstract event a refined event refines. These are what GRD
and SIM obligations are named after: the abstract label, not the concrete one. -/
private def abstractEvents (p : Project) (machine : String) (ev : Elem) :
    List (String × Elem) :=
  match lookupComponent p machine with
  | none => []
  | some m =>
    let abstractMachine := (childrenOf m.elem "refinesMachine").filterMap targetName |>.head?
    match abstractMachine.bind (lookupComponent p ·) with
    | none => []
    | some a =>
      let targets := eventTargets ev
      targets.filterMap fun target =>
        (childrenOf a.elem "event").find? (fun candidate => labelOf candidate == target)
          |>.map (fun ae => (a.name, ae))

private def abstractEvent (p : Project) (machine : String) (ev : Elem) :
    Option (String × Elem) :=
  let refs := abstractEvents p machine ev
  refs.head?

private def disjoin : List Term → Option Term
  | [] => none
  | term :: terms => some (terms.foldl (fun acc next => .bin "∨" acc next) term)

private def conjoin : List Term → Option Term
  | [] => some (.id "⊤")
  | term :: terms => some (terms.foldl (fun acc next => .bin "∧" acc next) term)

structure WdContext where
  theory : Theory.Env
  roots : List String
  totalKeywords : List String
  env : List (String × Ty)

private def totalKeywords (theory : Theory.Env) (roots : List String) : List String :=
  Theory.namesWithApplication theory roots .total

private def wdTop : Term := .id "⊤"

private def wdIsTop : Term → Bool
  | .id "⊤" => true
  | _ => false

private def wdAtoms : Term → List Term
  | .id "⊤" => []
  | .bin "∧" a b => wdAtoms a ++ wdAtoms b
  | t => [t]

private def wdDedupAux (seen : List Term) : List Term → List Term
  | [] => seen.reverse
  | t :: ts =>
      if seen.contains t then wdDedupAux seen ts else wdDedupAux (t :: seen) ts

private def wdDedup (ts : List Term) : List Term := wdDedupAux [] ts

private def wdBuild : List Term → Term
  | [] => wdTop
  | t :: ts => ts.foldl (fun acc next => .bin "∧" acc next) t

private def wdAnd (a b : Term) : Term :=
  wdBuild (wdDedup (wdAtoms a ++ wdAtoms b))

private def wdDrop (known : List Term) : Term → Term
  | .id "⊤" => wdTop
  | .bin "∧" a b => wdAnd (wdDrop known a) (wdDrop known b)
  | .bin "⇒" p q =>
      let q := wdDrop (known ++ wdAtoms p) q
      if wdIsTop q then wdTop else .bin "⇒" p q
  | .bind k pat body =>
      let body := wdDrop known body
      if wdIsTop body then wdTop else .bind k pat body
  | t => if known.contains t then wdTop else t

private def wdImpliesKnown (known : List Term) (p q : Term) : Term :=
  let q := wdDrop (known ++ wdAtoms p) q
  if wdIsTop q || wdIsTop p then q else .bin "⇒" p q

private def wdImplies (p q : Term) : Term := wdImpliesKnown [] p q

private def wdType : Ty → Term
  | .given n => .id n
  | .int => .id "ℤ"
  | .bool => .id "BOOL"
  | .pow t => .pre "ℙ" (wdType t)
  | .prod a b => .bin "×" (wdType a) (wdType b)
  | .mvar n => .id s!"?{n}"

private def actionFeasibility (types : List (String × Ty)) (action : Elem) : Option Term :=
  match attrOf action "assignment" with
  | none => none
  | some source =>
      match Formula.parse source with
      | .ok (.bin ":∈" _ set) => some (.bin "≠" set (.set []))
      | .ok (.bin ":∣" _ predicate) =>
          let targets := assignedBy action
          let binders := targets.filterMap fun v =>
            (types.find? (fun pair => pair.1 == v)).map fun (_, type) =>
              .bin "⦂" (.id (v ++ "'")) (wdType type)
          if binders.length == targets.length then
            some (binders.foldr (fun binder body => .bind "∃" binder body) predicate)
          else none
      | _ => none

private def wdFunctionType (context : WdContext) (f : Term) : Option Term :=
  match inferTermAt context.theory context.roots context.env f with
  | .ok (.pow (.prod a b)) => some (.bin "⇸" (wdType a) (wdType b))
  | _ => none

private def wdNonempty (s : Term) : Term := .bin "≠" s (.set [])

private def wdFreshName (base : String) (used : List String) : Nat → Nat → String
  | _, 0 => base ++ s!"{used.length + 1}"
  | index, fuel + 1 =>
      let candidate := if index == 0 then base else base ++ s!"{index}"
      if used.contains candidate then wdFreshName base used (index + 1) fuel else candidate

private def wdBound (isMax : Bool) (s : Term) : Term :=
  let used := identifiers s
  let bName := wdFreshName "b" used 0 (used.length + 1)
  let xName := wdFreshName "x" (bName :: used) 0 (used.length + 1)
  let b := .id bName
  let x := .id xName
  let order := if isMax then .bin "≥" b x else .bin "≤" b x
  .bind "∃" b (.bind "∀" x (.bin "⇒" (.bin "∈" x s) order))

private def wdRule (rule : Definedness) (s : Term) : Term :=
  match rule with
  | .finite => .app (.id "finite") s
  | .nonempty => wdNonempty s
  | .lowerBound => wdBound false s
  | .upperBound => wdBound true s

private def wdRules (rules : List Definedness) (s : Term) : Term :=
  rules.foldl (fun acc rule => wdAnd acc (wdRule rule s)) wdTop

private def definednessFor (context : WdContext) (name : String) : List Definedness :=
  Theory.definedness? context.theory context.roots name

private def wdPattern : Term → Term
  | .bin "↦" a b => .bin "," (wdPattern a) (wdPattern b)
  | .bin "," a b => .bin "," (wdPattern a) (wdPattern b)
  | .bin "⦂" a t => .bin "⦂" (wdPattern a) t
  | t => t

mutual

def needsWD (totalKeywords : List String) : Term → Bool
  | .num _ | .id _ => false
  | .bin op a b =>
      op == "÷" || op == "mod" || op == "^" || needsWD totalKeywords a ||
        needsWD totalKeywords b
  | .pre op a => op == "⋂" || needsWD totalKeywords a
  | .post _ a => needsWD totalKeywords a
  | .app f a =>
      let head := match f with
        | .id n => if totalKeywords.contains n then false else true
        | _ => true
      head || needsWD totalKeywords f || needsWD totalKeywords a
  | .img r a => needsWD totalKeywords r || needsWD totalKeywords a
  | .set ts => needsWDAny totalKeywords ts
  | .bind _ p b => needsWD totalKeywords p || needsWD totalKeywords b

/-- `List.any needsWD` would hide the recursive call inside a closure, where the
equation compiler cannot see that it is applied to a subterm. Spelling the list
traversal out keeps the whole thing structural. -/
def needsWDAny (totalKeywords : List String) : List Term → Bool
  | [] => false
  | t :: ts => needsWD totalKeywords t || needsWDAny totalKeywords ts

end

mutual

private def wdTermAux : Nat → WdContext → Term → Option Term
  | 0, _, _ => none
  | _, _, .num _ | _, _, .id _ => some wdTop
  | fuel + 1, context, .bin op a b => do
      let wa ← wdTermAux fuel context a
      let wb ← wdTermAux fuel context b
      if op == "∧" || op == "⇒" then
        return wdAnd wa (wdImpliesKnown (wdAtoms wa) a wb)
      if op == "∨" then
        return if wdIsTop wb then wa else wdAnd wa (.bin "∨" a wb)
      if op == "÷" then
        return wdAnd (wdAnd wa wb) (.bin "≠" b (.num 0))
      if op == "mod" then
        return wdAnd (wdAnd wa wb)
          (.bin "∧" (.bin "≤" (.num 0) a) (.bin "<" (.num 0) b))
      if op == "^" then
        return wdAnd (wdAnd wa wb) (.bin "≤" (.num 0) b)
      return wdAnd wa wb
  | fuel + 1, context, .pre op a => do
      let wa ← wdTermAux fuel context a
      if op == "⋂" then return (wdAnd wa (wdNonempty a))
      return wa
  | fuel + 1, context, .post _ a => wdTermAux fuel context a
  | fuel + 1, context, .app f a => do
      let wa ← wdTermAux fuel context a
      match f with
      | .id n =>
          let rules := definednessFor context n
          if !rules.isEmpty then return wdAnd wa (wdRules rules a)
          if context.totalKeywords.contains n then return wa
          else
            let wf ← wdTermAux fuel context f
            let ft ← wdFunctionType context f
            return wdAnd (wdAnd (wdAnd wf wa)
              (.bin "∈" a (.app (.id "dom") f)))
              (.bin "∈" f ft)
      | _ =>
          let wf ← wdTermAux fuel context f
          let ft ← wdFunctionType context f
          return wdAnd (wdAnd (wdAnd wf wa)
            (.bin "∈" a (.app (.id "dom") f)))
            (.bin "∈" f ft)
  | fuel + 1, context, .img r a => do
      let wr ← wdTermAux fuel context r
      let wa ← wdTermAux fuel context a
      return wdAnd wr wa
  | fuel + 1, context, .set ts => wdTerms fuel context ts
  | fuel + 1, context, .bind k pat body =>
      if k == "∀" || k == "∃" then do
        let wb ← wdTermAux fuel context body
        if wdIsTop wb then return wdTop
        if (patternNames pat).all (fun n => !(identifiers wb).contains n) then
          return wb
        return .bind k pat wb
      else
        match body with
        | .bin "∣" pred expr => do
            let wp ← wdTermAux fuel context pred
            let we ← wdTermAux fuel context expr
            let w := wdAnd wp (wdImplies pred we)
            return if wdIsTop w then wdTop else
              if k == "λ" || k == "{" then .bind "∀" (wdPattern pat) w else w
        | _ => wdTermAux fuel context body

private def wdTerms : Nat → WdContext → List Term → Option Term
  | 0, _, _ => none
  | _, _, [] => some wdTop
  | fuel + 1, context, t :: ts => do
      let wt ← wdTermAux fuel context t
      let ws ← wdTerms fuel context ts
      return wdAnd wt ws

end

mutual

private def wdFuel : Term → Nat
  | .id _ | .num _ => 1
  | .bin _ a b => wdFuel a + wdFuel b + 1
  | .pre _ a | .post _ a => wdFuel a + 1
  | .app f a | .img f a => wdFuel f + wdFuel a + 1
  | .set ts => wdFuelList ts + 1
  | .bind _ p b => wdFuel p + wdFuel b + 1

private def wdFuelList : List Term → Nat
  | [] => 0
  | t :: ts => wdFuel t + wdFuelList ts + 1

end

private def wdTerm (theory : Theory.Env) (roots totalKeywords : List String)
    (env : List (String × Ty)) (t : Term) : Option Term :=
  wdTermAux (wdFuel t + 1) { theory, roots, totalKeywords, env } t

private def wdRequired (totalKeywords : List String) (formula : String) : Bool :=
  match Formula.parse formula with
  | .ok t => needsWD totalKeywords t
  | .error _ => false

private def assignmentRhs (formula : String) : Option String :=
  match Formula.parse formula with
  | .ok (.bin op _ rhs) =>
      if op == "≔" || op == ":∈" || op == ":∣" then some (Formula.print rhs) else none
  | _ => none

private def assignmentRhsMode (strict : Bool) (formula : String) : Option String :=
  if strict then
    match Formula.parse formula with
    | .ok (.bin "≔" lhs rhs) =>
        let lhsArgs := Formula.flattenCommas lhs |>.filterMap fun term =>
          match term with
          | .app _ _ => some (Formula.print term)
          | _ => none
        some (String.intercalate " ∧ " (lhsArgs ++ [Formula.print rhs]))
    | .ok (.bin op _ rhs) =>
        if op == ":∈" || op == ":∣" then some (Formula.print rhs) else none
    | _ => none
  else assignmentRhs formula

private def wdGoal (theory : Theory.Env) (roots totalKeywords : List String)
    (env : List (String × Ty)) (formula : String) : Option Term :=
  match Formula.parse formula with
  | .ok t => wdTerm theory roots totalKeywords env t
  | .error _ => none

private def assignmentWdGoal (strict : Bool) (theory : Theory.Env)
    (roots totalKeywords : List String)
    (types : List (String × Ty)) (action : Elem) : Option Term := do
  let source ← attrOf action "assignment"
  let parsed ← Formula.parse source |>.toOption
  match parsed with
  | .bin "≔" lhs rhs =>
      if !strict then
        let rhs ← assignmentRhs source
        wdGoal theory roots totalKeywords types rhs
      else
        let lhsTerms := Formula.flattenCommas lhs |>.filterMap fun term =>
          match term with
          | .app _ _ => some term
          | _ => none
        let terms := lhsTerms ++ Formula.flattenCommas rhs
        let goals ← terms.mapM fun term =>
          wdGoal theory roots totalKeywords types (Formula.print term)
        pure (goals.foldl wdAnd wdTop)
  | .bin ":∣" _ predicate =>
      let body ← wdGoal theory roots totalKeywords types (Formula.print predicate)
      if !strict then some body else
        let binders := (assignedBy action).filterMap fun name =>
          (types.find? (fun pair => pair.1 == name)).map fun (_, type) =>
            .bin "⦂" (.id (name ++ "'")) (wdType type)
        if binders.length == (assignedBy action).length then
          some (binders.foldr (fun binder body => .bind "∀" binder body) body)
        else none
  | _ =>
      let rhs ← assignmentRhsMode strict source
      wdGoal theory roots totalKeywords types rhs

private def variantType (theory : Theory.Env) (roots : List String)
    (types : List (String × Ty)) (variant : Elem) : Option Ty := do
  let source ← attrOf variant "expression"
  let term ← Formula.parse source |>.toOption
  (inferTermAt theory roots types term).toOption

private def variantTerm (variant : Elem) : Option Term := do
  let source ← attrOf variant "expression"
  Formula.parse source |>.toOption

private def witnessFeasibility (types visibleParams : List (String × Ty))
    (witness : Elem) : Option Term := do
  let predicate ← Formula.parse ((attrOf witness "predicate").getD "") |>.toOption
  let witnessVar ← witnessVariable witness
  let (_, type) ← (visibleParams.find? (fun pair => pair.1 == witnessVar) <|>
    types.find? (fun pair => pair.1 == witnessVar))
  some (.bind "∃" (.bin "⦂" (.id witnessVar) (wdType type)) predicate)

/- Rules tried against the corpus and rejected by measurement, recorded so they are not
retried. Each was plausible and each made the gates worse:

- Skip INV for typing-shaped invariants (`v ∈ T` or `v ⊆ T` where `T` mentions no
  variable of the machine), first for the variable. Names 1105 -> 1058, statements
  856/1033 -> 813/883. It removes 150 spurious obligations at the cost of 47 real ones.
  Precision improves and recall falls, which is the wrong trade here: a missing
  obligation is unsound, a spurious one is only wasted work. Rodin does emit INV for
  typing invariants.
- Skip GRD and SIM when the concrete event restates the abstract label. 1002 -> 971,
  and inverted: Rodin generates SIM precisely when the label is restated.
- Skip INV for typing-shaped invariants by the cruder test "right-hand side mentions no
  variable at all". 1002 -> 955.
- Give INITIALISATION *no* hypotheses at all, on the reasoning that no invariant holds
  before the machine starts. Too strong: Rodin's INITIALISATION sequents carry 12 to 14
  hypotheses, and only 3 carry none. The refinement that works, and that `generate` now
  does, is to give it the context axioms but not the invariants. Axioms hold always; the
  invariants are what initialisation has to establish.
- Emit `WD(P ∨ Q)` as the logically equivalent `WD(P) ∧ (¬P ⇒ WD(Q))`. Rodin's
  normal form is `WD(P) ∧ (P ∨ WD(Q))`; the implication spelling loses WD matches.
-/

/-- The standing hypotheses for non-initialization obligations: every axiom of every
context in the dependency closure, then every invariant up the refinement chain, in
declaration order. `closure` already computes that order for the typechecker, so the two
cannot drift apart. -/
def contextHyps (p : Project) (name : String) : List Term :=
  let (_, order) := closure p [] name
  order.flatMap fun dep =>
    match lookupComponent p dep with
    | none => []
    | some c =>
      (childrenOf c.elem "axiom" ++ childrenOf c.elem "invariant").filterMap fun a =>
        (Formula.parse ((attrOf a "predicate").getD "")).toOption

private def contextAxioms (p : Project) (name : String) : List Term :=
  let (_, order) := closure p [] name
  order.flatMap fun dep =>
    match lookupComponent p dep with
    | none => []
    | some c => (childrenOf c.elem "axiom").filterMap fun a =>
        (Formula.parse ((attrOf a "predicate").getD "")).toOption

private def hypothesesBefore (p : Project) (name : String) (target : Elem) : List Term :=
  let (_, order) := closure p [] name
  order.flatMap fun dep =>
    match lookupComponent p dep with
    | none => []
    | some c =>
      let declarations := childrenOf c.elem "axiom" ++ childrenOf c.elem "invariant"
      (if dep == name then beforeElem target declarations else declarations).filterMap fun a =>
        (Formula.parse ((attrOf a "predicate").getD "")).toOption

private def eventHypsBefore (p : Project) (name : String) (ev target : Elem) : List Term :=
  let base := if labelOf ev == "INITIALISATION" then contextAxioms p name
    else contextHyps p name
  base ++ (beforeElem target (effectiveGuards p name ev)).filterMap fun g =>
    (Formula.parse ((attrOf g "predicate").getD "")).toOption

private def eventHyps (p : Project) (name : String) (ev : Elem) : List Term :=
  let base := if labelOf ev == "INITIALISATION" then contextAxioms p name
    else contextHyps p name
  base ++ (effectiveGuards p name ev).filterMap fun g =>
    (Formula.parse ((attrOf g "predicate").getD "")).toOption

/-- Obligations for one machine or context under a native theory environment. -/
private def generateInMode (strict : Bool) (theory : Theory.Env) (p : Project)
    (name : String) : List Obligation := Id.run do
  match lookupComponent p name with
  | none => return []
  | some c =>
    let isMachine := c.elem.tag == "org.eventb.core.machineFile"
    let roots := componentTheoryRoots p name
    let (types, eventParams, diagnostics) := match
        (if strict then inferComponentDetailsCheckedIn theory p name
         else inferComponentDetailsIn theory p name) with
      | .ok result => (result.types, result.eventParams, result.diagnostics)
      | .error error => ([], [], [error.message])
    let finalize := fun obligations : List Obligation => obligations.map fun obligation =>
      { obligation with
          component := name
          theoryRoots := roots
          diagnostics := diagnostics
          goal := obligation.goal.map (Theory.normalize theory roots)
          hyps := obligation.hyps.map (Theory.normalize theory roots) }
    let total := totalKeywords theory roots
    let mut out : List Obligation := []
    -- A `theorem` invariant or axiom must follow from what precedes it.
    for a in childrenOf c.elem "axiom" ++ childrenOf c.elem "invariant" do
      if (attrOf a "theorem").getD "false" == "true" then
        -- A theorem's goal is simply its own predicate: it claims to follow from what
        -- precedes it, so nothing is substituted.
        out := out ++ [{ name := labelOf a ++ "/THM", kind := "THM",
                         goal := (Formula.parse ((attrOf a "predicate").getD "")).toOption,
                         hyps := hypothesesBefore p name a }]
    -- Well-definedness is named after the predicate alone in a context or an
    -- invariant, and under its event for a guard, action or witness.
    for a in childrenOf c.elem "axiom" ++ childrenOf c.elem "invariant" do
      if wdRequired total ((attrOf a "predicate").getD "") then
        out := out ++ [{ name := labelOf a ++ "/WD", kind := "WD",
                         goal := wdGoal theory roots total types
                           ((attrOf a "predicate").getD ""),
                         hyps := hypothesesBefore p name a }]
    -- A guard can be marked `theorem` too, and is then named under its event.
    for ev in childrenOf c.elem "event" do
      for g in childrenOf ev "guard" do
        if (attrOf g "theorem").getD "false" == "true" then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf g ++ "/THM", kind := "THM",
               goal := (Formula.parse ((attrOf g "predicate").getD "")).toOption,
               hyps := eventHypsBefore p name ev g }]
    if !isMachine then return finalize out
    let explicitVariants := childrenOf c.elem "variant"
    let hasConvergent := (childrenOf c.elem "event").any (fun event =>
      (attrOf event "convergence").getD "0" == "1")
    let variants := if explicitVariants.isEmpty &&
        !hasConvergent && (childrenOf c.elem "event").any (fun event =>
          (attrOf event "convergence").getD "0" == "2") then
      [.variant [("org.eventb.core.expression", "0")] []]
    else explicitVariants
    -- Rodin supplies a constant zero variant when a machine has anticipated events
    -- but no explicit variant.
    for variant in variants do
      let source := (attrOf variant "expression").getD ""
      if wdRequired total source then
        out := out ++
          [{ name := "VWD", kind := "VWD",
             goal := wdGoal theory roots total types source,
             hyps := contextHyps p name }]
      match variantTerm variant, variantType theory roots types variant with
      | some term, some (.pow _) =>
          out := out ++
            [{ name := "FIN", kind := "FIN", goal := some (.app (.id "finite") term),
               hyps := contextHyps p name }]
          for ev in childrenOf c.elem "event" do
            let convergence := (attrOf ev "convergence").getD "0"
            if convergence == "1" || convergence == "2" then
              let after := Formula.subst (eventStateSubstMode strict p name ev) term
              let relation := if convergence == "1" then "⊂" else "⊆"
              out := out ++
                [{ name := labelOf ev ++ "/VAR", kind := "VAR",
                   goal := some (.bin relation after term),
                   hyps := eventHyps p name ev ++ eventRelationalHypsMode strict p name ev }]
      | some term, some .int =>
          for ev in childrenOf c.elem "event" do
            let convergence := (attrOf ev "convergence").getD "0"
            if convergence == "1" || convergence == "2" then
              let nat := .bin "∈" term (.id "ℕ")
              out := out ++
                [{ name := labelOf ev ++ "/NAT", kind := "NAT", goal := some nat,
                   hyps := eventHyps p name ev }]
              let after := Formula.subst (eventStateSubstMode strict p name ev) term
              let relation := if convergence == "1" then "<" else "≤"
              out := out ++
                [{ name := labelOf ev ++ "/VAR", kind := "VAR",
                   goal := some (.bin relation after term),
                   hyps := eventHyps p name ev ++ eventRelationalHypsMode strict p name ev }]
      | _, _ => pure ()
    let invariants := childrenOf c.elem "invariant"
    for ev in childrenOf c.elem "event" do
      let base := if labelOf ev == "INITIALISATION" then contextAxioms p name
        else contextHyps p name
      let witnesses := (childrenOf ev "witness").filterMap fun witness =>
        if strict then witnessBinding witness else witnessSubstitution witness
      let witnessPredicates := (childrenOf ev "witness").filterMap fun w =>
        (Formula.parse ((attrOf w "predicate").getD "")).toOption
      let witnessConstraints := if strict then
          (childrenOf ev "witness").filterMap fun w =>
            if witnessBinding w |>.isSome then none
            else (Formula.parse ((attrOf w "predicate").getD "")).toOption
        else []
      let visibleParams := visibleEventBindings p eventParams name (labelOf ev)
      let concreteVariables := (childrenOf c.elem "variable").filterMap (attrOf · "identifier")
      let concreteActions := if strict then accurateTransitionActions p name ev
        else initializationActions p c ev
      let initialization := labelOf ev == "INITIALISATION"
      let concreteRelations :=
        concreteStateRelationsMode strict initialization concreteVariables concreteActions
      -- The concrete before-after predicate is the event's effective action list:
      -- parent actions are inherited only when the event is explicitly extended.
      -- Using `eventActions` here would fabricate parent updates for an ordinary
      -- refinement and make a frame/gluing INV or SIM obligation vacuous.
      let assigned := (eventStateSubstMode strict p name ev).map (·.1)
      -- An invariant needs re-proving only if the event can change something it
      -- mentions. This filter is what keeps the INV count at Rodin's 934 rather than
      -- events times invariants.
      for inv in invariants do
        if (attrOf inv "theorem").getD "false" != "true" then
          let free := freeOf ((attrOf inv "predicate").getD "")
          if labelOf ev == "INITIALISATION" || assigned.any (fun v => free.contains v) then
            -- The obligation is the invariant restated over the after-state, which is
            -- exactly the invariant with the event's assignments substituted in.
            let σ := eventStateSubstMode strict p name ev
            let goal := (Formula.parse ((attrOf inv "predicate").getD "")).toOption.map
              (fun predicate => Formula.subst witnesses (Formula.subst σ predicate))
            -- The event's guards hold when it fires, so they join the standing
            -- hypotheses.
            let guards := (effectiveGuards p name ev).filterMap fun g =>
              (Formula.parse ((attrOf g "predicate").getD "")).toOption
            let actionHyps :=
              (eventRelationalHypsMode strict p name ev).map (Formula.subst witnesses)
            out := out ++
              [{ name := labelOf ev ++ "/" ++ labelOf inv ++ "/INV", kind := "INV",
                 goal := goal, hyps := base ++ guards ++ actionHyps }]
      -- Refinement obligations are named after the abstract event's labels.
      let abstractRefs := abstractEvents p name ev
      if abstractRefs.length > 1 && !isExtended ev then
        let abstractPredicates := abstractRefs.filterMap fun (am, ae) =>
          let guards := (effectiveGuards p am ae).filterMap fun g =>
            (Formula.parse ((attrOf g "predicate").getD "")).toOption.map
              (Formula.subst witnesses)
          conjoin guards
        if let some goal := disjoin abstractPredicates then
          out := out ++
            [{ name := labelOf ev ++ "/MRG", kind := "MRG", goal := some goal,
                 hyps := base ++
                 ((effectiveGuards p name ev).filterMap fun g =>
                   (Formula.parse ((attrOf g "predicate").getD "")).toOption) ++
                 witnessConstraints ++ concreteRelations }]
      if let some (am, ae) := abstractEvent p name ev then
        if !isExtended ev then
          -- Guard strengthening: the concrete event must be enabled only where the
          -- abstract one is, so the goal is the abstract guard itself. A witness names
          -- the value an abstract parameter takes, and is substituted in when present.
          let concreteGuards := effectiveGuards p name ev
          if abstractRefs.length <= 1 then
            for g in effectiveGuards p am ae do
              let abstractPredicate := (Formula.parse ((attrOf g "predicate").getD "")).toOption
              let repeated := concreteGuards.any fun q =>
                match abstractPredicate, Formula.parse ((attrOf q "predicate").getD "") with
                | some abstractTerm, .ok concreteTerm =>
                    Formula.stripAscriptions abstractTerm == Formula.stripAscriptions concreteTerm
                | _, _ => false
              if !repeated then
                let goal := abstractPredicate.map (Formula.subst witnesses)
                out := out ++
                  [{ name := labelOf ev ++ "/" ++ labelOf g ++ "/GRD", kind := "GRD",
                     goal := goal, hyps := base ++ witnessConstraints ++
                       concreteGuards.filterMap fun q =>
                         (Formula.parse ((attrOf q "predicate").getD "")).toOption }]
          -- Simulation is required only for abstract variables declared by the concrete
          -- machine. A disappeared abstract variable is handled by a gluing invariant,
          -- not by inventing a raw after-state identifier in this sequent.
          let concrete := concreteActions.flatMap substOf
          let concreteTargets := concreteActions.flatMap assignedBy
          let concreteAfter := concreteActions.flatMap actionAfterSubst
          let initialization := labelOf ev == "INITIALISATION"
          let concreteRelations :=
            concreteStateRelationsMode strict initialization concreteVariables concreteActions
          for act in effectiveActions p am ae do
            let abstractRelation :=
              if strict then actionRelationAccurate act else actionRelation act
            let unchangedAfter := (assignedBy act).filter
                (fun v => !concreteTargets.contains v) |>.map fun v =>
              (v ++ "'", .id v)
            let eligible := (assignedBy act).all (fun v => concreteVariables.contains v)
            let simGoal : Option Term :=
              if !eligible then none else match abstractRelation, substOf act with
              | some abstractRelation, _ =>
                  some (Formula.subst (concreteAfter ++ unchangedAfter)
                    (Formula.subst witnesses abstractRelation))
              | none, abstractAssignments =>
                  let goals := abstractAssignments.filterMap fun (v, absRhs) =>
                    match concrete.find? (fun q : String × Term => q.1 == v) with
                    | some (_, conRhs) =>
                        some (Term.bin "=" conRhs (Formula.subst witnesses absRhs))
                    | none =>
                        if concreteVariables.contains v then
                          some (Term.bin "=" (.id (v ++ "'"))
                            (Formula.subst witnesses absRhs))
                        else
                          none
                  if goals.length == abstractAssignments.length then conjoin goals else none
            match simGoal with
            | some goal =>
                let needsActionRelation := abstractRelation.isSome ||
                  (concreteActions.any (fun q => !(nondeterministicSubst q).isEmpty))
                let frameRelations := if initialization then [] else
                  match abstractRelation, substOf act with
                  | none, abstractAssignments => abstractAssignments.filterMap fun (v, _) =>
                      if concreteVariables.contains v &&
                          !concreteTargets.contains v then
                        some (.bin "=" (.id (v ++ "'")) (.id v))
                      else none
                  | _, _ => []
                let actionHyps := if needsActionRelation then
                    concreteRelations ++ frameRelations
                  else frameRelations
                out := out ++
                  [{ name := labelOf ev ++ "/" ++ labelOf act ++ "/SIM", kind := "SIM",
                     goal := some goal, hyps := base ++ witnessConstraints ++
                       ((effectiveGuards p name ev).filterMap fun q =>
                         (Formula.parse ((attrOf q "predicate").getD "")).toOption) ++ actionHyps }]
            | none => pure ()
      let parentMachineNames := (childrenOf c.elem "refinesMachine").filterMap targetName
      let abstractMachineName : Option String :=
        match abstractRefs.head? with
        | some (am, _) => some am
        | none => parentMachineNames.head?
      let abstractMachine : Option Component := abstractMachineName.bind
        (fun am => lookupComponent p am)
      let abstractVariables := abstractMachine.toList.flatMap fun machine =>
        (childrenOf machine.elem "variable").filterMap (attrOf · "identifier")
      let abstractTargets := abstractRefs.flatMap fun (am, ae) =>
        match lookupComponent p am with
        | none => []
        | some _ => (effectiveActions p am ae).flatMap assignedBy
      let concreteActions := if strict then accurateTransitionActions p name ev
        else initializationActions p c ev
      let concreteTargets := concreteActions.flatMap assignedBy
      for v in abstractVariables do
        if concreteVariables.contains v && concreteTargets.contains v &&
            !abstractTargets.contains v then
          let actionHyps := concreteActions.filter (fun action => (assignedBy action).contains v)
            |>.flatMap actionAfterRelation
          out := out ++
            [{ name := labelOf ev ++ "/" ++ v ++ "/EQL", kind := "EQL",
               goal := some (.bin "=" (.id (v ++ "'")) (.id v)),
               hyps := base ++ actionHyps }]
      for g in childrenOf ev "guard" do
        if wdRequired total ((attrOf g "predicate").getD "") then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf g ++ "/WD", kind := "WD",
               goal := wdGoal theory roots total types ((attrOf g "predicate").getD ""),
               hyps := eventHypsBefore p name ev g }]
      let wdActions := if strict then accurateTransitionActions p name ev
        else initializationActions p c ev
      for act in wdActions do
        if let some source := attrOf act "assignment" then
          if let some rhs := assignmentRhsMode strict source then
            if wdRequired total rhs then
              out := out ++
                [{ name := labelOf ev ++ "/" ++ labelOf act ++ "/WD", kind := "WD",
                   goal := assignmentWdGoal strict theory roots total types act,
                   hyps := eventHyps p name ev }]
        if let some goal := actionFeasibility types act then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf act ++ "/FIS", kind := "FIS",
               goal := some goal, hyps := eventHyps p name ev ++ witnessPredicates }]
      for w in childrenOf ev "witness" do
        let witnessAfter := match witnessVariable w with
          | some v =>
              let after := if v.endsWith "'" then v else v ++ "'"
              witnessPredicates.any (fun predicate => (identifiers predicate).contains after)
          | none => false
        out := out ++
          [{ name := labelOf ev ++ "/" ++ labelOf w ++ "/WFIS", kind := "WFIS",
             goal := witnessFeasibility types visibleParams w,
             hyps := eventHyps p name ev ++ if witnessAfter then concreteRelations else [] }]
        if wdRequired total ((attrOf w "predicate").getD "") then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf w ++ "/WWD", kind := "WWD",
               -- Rodin records witness WD as a hypothesis-only sequent.
               hyps := eventHyps p name ev ++
                 (wdGoal theory roots total types ((attrOf w "predicate").getD "")).toList }]
    return finalize out

/-- Fail-closed wrapper for front ends that must not consume partial POG output. The
compatibility `generateIn` API keeps diagnostics on each obligation for reporting and
comparison, while this API refuses any scope with typing or resolution errors. -/
def generateCheckedIn (theory : Theory.Env) (p : Project) (name : String) :
    Except EventB.Error (List Obligation) :=
  match lookupComponent p name with
  | none => .error (EventB.Error.typing
      s!"cannot generate trusted obligations for missing component {name}")
  | some _ =>
      match inferComponentDetailsCheckedIn theory p name with
      | .error error => .error error
      | .ok details =>
          let diagnostics := details.diagnostics
          if !diagnostics.isEmpty then
            .error (EventB.Error.typing (s!
              "cannot generate trusted obligations for {name}: " ++
                String.intercalate "; " diagnostics))
          else
            let obligations := generateInMode true theory p name
            match obligations.find? (fun obligation => !obligation.diagnostics.isEmpty) with
            | none =>
                match obligations.find? (fun obligation => !obligation.shapeValid) with
                | none => .ok obligations
                | some obligation => .error (EventB.Error.typing (s!
                    "cannot generate trusted obligations for {name}: malformed " ++
                      obligation.kind ++ " obligation " ++ obligation.name))
            | some obligation =>
                .error (EventB.Error.typing (s!
                  "cannot generate trusted obligations for {name}: " ++
                    String.intercalate "; " obligation.diagnostics))

/-- Exact provenance for a generated EQL obligation.  This retains the source
    elements used by the generator instead of reconstructing them from the PO name
    at a later trust boundary. -/
structure EqlOrigin where
  component : String
  event : String
  eqlVariable : String
  concreteEvent : Elem
  abstractMachine : String
  abstractRefs : List (String × Elem)
  effectiveActions : List Elem
  actionHyps : List Formula.Term
  deriving BEq, Repr

private def directVariables (component : Component) : List String :=
  (childrenOf component.elem "variable").filterMap (attrOf · "identifier")

private def exactEqlGoal (varName : String) : Formula.Term :=
  .bin "=" (.id (varName ++ "'")) (.id varName)

/-- Locate the exact EQL record and the exact source event/action slice that caused
    it. `none` means this event/variable pair does not satisfy Rodin's EQL condition;
    malformed or unchecked projects return an error. -/
def locateEql? (theory : Theory.Env) (p : Project)
    (component event eqlVariable : String) :
    Except EventB.Error (Option (EqlOrigin × Obligation)) := do
  let generated ← generateCheckedIn theory p component
  let concrete ← match lookupComponent p component with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate EQL source in missing component {component}")
  let concreteEvent ← match (childrenOf concrete.elem "event").find?
      (fun candidate => labelOf candidate == event) with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate EQL source event {component}/{event}")
  let abstractRefs := abstractEvents p component concreteEvent
  let abstractMachineName : Option String :=
    match abstractRefs.head? with
    | some (machine, _) => some machine
    | none => (childrenOf concrete.elem "refinesMachine").filterMap targetName |>.head?
  let abstractMachine ← match abstractMachineName.bind (lookupComponent p ·) with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate EQL abstract machine for {component}/{event}")
  let concreteActions := accurateTransitionActions p component concreteEvent
  let concreteVariables := directVariables concrete
  let abstractVariables := directVariables abstractMachine
  let concreteTargets := concreteActions.flatMap assignedBy
  let abstractTargets := abstractRefs.flatMap fun (machine, abstractEvent) =>
    match lookupComponent p machine with
    | some _ => (effectiveActions p machine abstractEvent).flatMap assignedBy
    | none => []
  unless concreteVariables.contains eqlVariable && abstractVariables.contains eqlVariable &&
      concreteTargets.contains eqlVariable && !abstractTargets.contains eqlVariable do
    return none
  let name := event ++ "/" ++ eqlVariable ++ "/EQL"
  let goal := exactEqlGoal eqlVariable
  let obligation ← match generated.find? (fun candidate =>
      candidate.kind == "EQL" && candidate.name == name && candidate.goal == some goal) with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"checked generator has no exact EQL obligation {component}/{name}")
  let actionHyps := concreteActions.filter (fun action =>
    (assignedBy action).contains eqlVariable) |>.flatMap actionAfterRelation
  let origin : EqlOrigin :=
    { component := component
      event := event
      eqlVariable := eqlVariable
      concreteEvent := concreteEvent
      abstractMachine := abstractMachine.name
      abstractRefs := abstractRefs
      effectiveActions := concreteActions
      actionHyps := actionHyps }
  pure (some (origin, obligation))

/- The witness and simulation locators below deliberately sit on the same private
   selectors as generateInMode. A PO name is only accepted after its source
   element has been selected uniquely and the checked generator has emitted the
   corresponding obligation. -/

def exactWitnessBinding? (witness : Elem) : Option (String × Formula.Term) :=
  witnessBinding witness

def exactWitnessVariable? (witness : Elem) : Option String :=
  witnessVariable witness

def exactWitnessPredicate? (witness : Elem) : Option Formula.Term :=
  (attrOf witness "predicate").bind (Formula.parse · |>.toOption)

structure WitnessOrigin where
  component : String
  event : String
  witnessLabel : String
  concreteEvent : Elem
  witness : Elem
  witnessVariable : String
  predicate : Formula.Term
  binding : Option (String × Formula.Term)
  deriving BEq, Repr

private def uniqueChildByLabel (parent : Elem) (tag label : String) : Option Elem :=
  match (childrenOf parent tag).filter (fun child => labelOf child == label) with
  | [child] => some child
  | _ => none

private def checkedWitnessOrigin (component event witnessLabel : String)
    (concreteEvent witness : Elem) (predicate : Formula.Term)
    (witnessName : String) : WitnessOrigin :=
  { component
    event
    witnessLabel
    concreteEvent
    witness
    witnessVariable := witnessName
    predicate
    binding := exactWitnessBinding? witness }

/-- Locate a uniquely named witness and its checked WFIS/WWD obligation.

    kind is explicit because the same witness can generate both WFIS and WWD, while
    the source identity is shared. Ambiguous source labels and duplicate generated
    names fail closed. -/
def locateWitness? (theory : Theory.Env) (p : Project)
    (component event witnessLabel kind : String) :
    Except EventB.Error (Option (WitnessOrigin × Obligation)) := do
  if kind != "WFIS" && kind != "WWD" then
    throw (EventB.Error.typing s!"unsupported witness obligation kind {kind}")
  let generated ← generateCheckedIn theory p component
  let concrete ← match lookupComponent p component with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate witness source in missing component {component}")
  let concreteEvent ← match uniqueChildByLabel concrete.elem "event" event with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate unique witness source event {component}/{event}")
  let witness ← match uniqueChildByLabel concreteEvent "witness" witnessLabel with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate unique witness {component}/{event}/{witnessLabel}")
  let predicate ← match exactWitnessPredicate? witness with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot parse witness predicate {component}/{event}/{witnessLabel}")
  let witnessName ← match exactWitnessVariable? witness with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot resolve witness variable {component}/{event}/{witnessLabel}")
  let details ← inferComponentDetailsCheckedIn theory p component
  let visibleParams := visibleEventBindings p details.eventParams component event
  let expectedGoal :=
    if kind == "WFIS" then
      (witnessFeasibility details.types visibleParams witness).map
        (Theory.normalize theory (componentTheoryRoots p component))
    else none
  let name := event ++ "/" ++ witnessLabel ++ "/" ++ kind
  let candidates := generated.filter (fun obligation =>
    obligation.kind == kind && obligation.name == name && obligation.goal == expectedGoal)
  let obligation ← match candidates with
    | [] => return none
    | [value] => pure value
    | _ => throw (EventB.Error.typing
        s!"checked generator emitted duplicate witness obligation {component}/{name}")
  if kind == "WFIS" && expectedGoal.isNone then
    throw (EventB.Error.typing
      s!"witness feasibility has no typed goal {component}/{event}/{witnessLabel}")
  if kind == "WWD" && expectedGoal.isSome then
    throw (EventB.Error.typing
      s!"witness definedness unexpectedly has a goal {component}/{event}/{witnessLabel}")
  pure (some (checkedWitnessOrigin component event witnessLabel concreteEvent witness
    predicate witnessName, obligation))

structure SimOrigin where
  component : String
  event : String
  concreteEvent : Elem
  abstractMachine : String
  abstractEvent : Elem
  abstractRefs : List (String × Elem)
  abstractAction : Elem
  concreteActions : List Elem
  deriving BEq, Repr

/-- Locate the exact abstract event/action behind one generated SIM obligation.

    The selected abstract action is unique by label in the effective action slice;
    this rejects a name-only match when malformed input would produce duplicate PO
    names. -/
def locateSim? (theory : Theory.Env) (p : Project)
    (component event abstractActionLabel : String) :
    Except EventB.Error (Option (SimOrigin × Obligation)) := do
  let generated ← generateCheckedIn theory p component
  let concrete ← match lookupComponent p component with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate SIM source in missing component {component}")
  let concreteEvent ← match uniqueChildByLabel concrete.elem "event" event with
    | some value => pure value
    | none => throw (EventB.Error.typing
        s!"cannot locate unique SIM source event {component}/{event}")
  if isExtended concreteEvent then return none
  let refs := abstractEvents p component concreteEvent
  let (abstractMachine, abstractEvent) ← match refs with
    | [(machine, value)] => pure (machine, value)
    | _ => return none
  match lookupComponent p abstractMachine with
  | none => throw (EventB.Error.typing
      s!"cannot locate SIM abstract component {abstractMachine}")
  | some _ => pure ()
  let abstractActions := effectiveActions p abstractMachine abstractEvent
  let matchingActions := abstractActions.filter
    (fun action => labelOf action == abstractActionLabel)
  let abstractAction ← match matchingActions with
    | [value] => pure value
    | [] => return none
    | _ => throw (EventB.Error.typing
        s!"ambiguous SIM abstract action {abstractMachine}/{abstractActionLabel}")
  let name := event ++ "/" ++ abstractActionLabel ++ "/SIM"
  let candidates := generated.filter (fun obligation =>
    obligation.kind == "SIM" && obligation.name == name)
  let obligation ← match candidates with
    | [] => return none
    | [value] => pure value
    | _ => throw (EventB.Error.typing
        s!"checked generator emitted duplicate SIM obligation {component}/{name}")
  pure (some
    ({ component
       event
       concreteEvent
       abstractMachine
       abstractEvent
       abstractRefs := refs
       abstractAction := abstractAction
       concreteActions := accurateTransitionActions p component concreteEvent }, obligation))

def simSourceBound (theory : Theory.Env) (p : Project)
    (component event abstractActionLabel : String) (target : Obligation) : Bool :=
  match locateSim? theory p component event abstractActionLabel with
  | .ok (some (_, obligation)) => obligation == target
  | _ => false

/-- Bind generated names to the source slice selected by the generator.  In
    particular, GRD and SIM labels come from the selected abstract event, while
    FIS/WD labels come from the concrete transition action slice. -/
def generatedSourceBound (p : Project) (obligation : Obligation) : Bool :=
  let directComponent := lookupComponent p obligation.component
  let directEvent (event : String) : Option Elem :=
    directComponent.bind fun component =>
      (childrenOf component.elem "event").find? (fun candidate => labelOf candidate == event)
  let hasDirectLabel (tag label : String) : Bool :=
    directComponent.any fun component =>
      (childrenOf component.elem tag).any (fun child => labelOf child == label)
  let hasEventChild (event tag label : String) : Bool :=
    (directEvent event).any fun current =>
      (childrenOf current tag).any (fun child => labelOf child == label)
  let hasVariant := directComponent.any fun component =>
    (childrenOf component.elem "variant").any (fun _ => true)
  let parts := obligation.name.splitOn "/"
  match obligation.kind, parts with
  | "INV", [event, label, _] =>
      (directEvent event).isSome &&
        (let (_, closure) := EventB.Typing.closure p [] obligation.component
         closure.any fun name =>
           (lookupComponent p name).any fun component =>
             (childrenOf component.elem "invariant").any
               (fun child => labelOf child == label) ||
             (childrenOf component.elem "axiom").any
               (fun child => labelOf child == label))
  | "GRD", [event, label, _] =>
      (directEvent event).any fun concrete =>
        !isExtended concrete &&
        (abstractEvents p obligation.component concrete).length <= 1 &&
        (abstractEvent p obligation.component concrete).any fun (machine, target) =>
          (effectiveGuards p machine target).any (fun guard => labelOf guard == label)
  | "SIM", [event, label, _] =>
      (directEvent event).any fun concrete =>
        !isExtended concrete &&
        (abstractEvents p obligation.component concrete).length <= 1 &&
        (abstractEvent p obligation.component concrete).any fun (machine, target) =>
          (effectiveActions p machine target).any (fun action => labelOf action == label)
  | "FIS", [event, label, _] =>
      (directEvent event).any fun concrete =>
        (accurateTransitionActions p obligation.component concrete).any
          (fun action => labelOf action == label)
  | "WFIS", [event, label, _] | "WWD", [event, label, _] =>
      hasEventChild event "witness" label
  | "EQL", [event, eqlVariable, _] =>
      (directEvent event).any fun concrete =>
        let abstractRefs := abstractEvents p obligation.component concrete
        let abstractMachineName : Option String :=
          match abstractRefs.head? with
          | some (machine, _) => some machine
          | none => (childrenOf concrete "refinesMachine").filterMap targetName |>.head?
        let abstractVariables := abstractMachineName.bind (lookupComponent p ·) |>.any
          (fun machine => directVariables machine |>.contains eqlVariable)
        let concreteActions := accurateTransitionActions p obligation.component concrete
        let concreteVariables := directComponent.any
          (fun component => directVariables component |>.contains eqlVariable)
        let concreteTargets := concreteActions.flatMap assignedBy
        let abstractTargets := abstractRefs.flatMap fun (machine, target) =>
          (effectiveActions p machine target).flatMap assignedBy
        abstractVariables && concreteVariables && concreteTargets.contains eqlVariable &&
          !abstractTargets.contains eqlVariable
  | "WD", [event, label, _] =>
      hasEventChild event "guard" label ||
        hasEventChild event "action" label ||
        hasEventChild event "witness" label ||
        (directEvent event).any fun concrete =>
          (accurateTransitionActions p obligation.component concrete).any
            (fun action => labelOf action == label)
  | "WD", [label, _] | "THM", [label, _] => hasDirectLabel "invariant" label ||
      hasDirectLabel "axiom" label
  | "MRG", [event, _] =>
      (directEvent event).any fun concrete =>
        !isExtended concrete &&
          (eventRefinementTargets p obligation.component event).length > 1
  | "VAR", [event, _] | "NAT", [event, _] =>
      (directEvent event).isSome
  | "VWD", ["VWD"] | "FIN", ["FIN"] => hasVariant
  | _, _ => false

/-- Compatibility entry point for Rodin corpus projects without user theories. -/
def generate (p : Project) (name : String) : List Obligation :=
  generateInMode false Theory.empty p name

def generateIn (theory : Theory.Env) (p : Project) (name : String) : List Obligation :=
  generateInMode false theory p name

def generateChecked (p : Project) (name : String) : Except EventB.Error (List Obligation) :=
  generateCheckedIn Theory.empty p name

private def checkedMissingProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.seesContext [("org.eventb.core.target", "Missing")] []] }]

private def defaultInitializationProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "inv"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          []] }]

private def rightWitnessProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "inv"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "step")]
          [.parameter [("org.eventb.core.identifier", "p")] []
           , .guard [("org.eventb.core.label", "g"),
                     ("org.eventb.core.predicate", "p > 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ p")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .event [("org.eventb.core.label", "INITIALISATION")] []
          , .event [("org.eventb.core.label", "step")]
            [.refinesEvent [("org.eventb.core.target", "step")] []
             , .parameter [("org.eventb.core.identifier", "q")] []
             , .guard [("org.eventb.core.label", "g"),
                       ("org.eventb.core.predicate", "q + 1 > 0")] []
             , .witness [("org.eventb.core.label", "p"),
                         ("org.eventb.core.predicate", "q + 1 = p")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ q + 1")] []]] }]

private def hiddenParameterChild : Component :=
  { name := "C"
    elem := .machineFile [("org.eventb.core.name", "C")]
      [.refinesMachine [("org.eventb.core.target", "B")] []
       , .variable [("org.eventb.core.identifier", "x")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "step")]
         [.refinesEvent [("org.eventb.core.target", "step"),
                         ("org.eventb.core.extended", "true")] []
          , .guard [("org.eventb.core.label", "hidden"),
                    ("org.eventb.core.predicate", "p = 0")] []]] }

private def dataRefinementProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "a")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "a ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "a ≔ 0")] []]
        , .event [("org.eventb.core.label", "step")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "a ≔ a + 1")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "b")] []
          , .invariant [("org.eventb.core.label", "type"),
                        ("org.eventb.core.predicate", "b ∈ ℤ")] []
          , .invariant [("org.eventb.core.label", "glue"),
                        ("org.eventb.core.predicate", "a = b")] []
          , .event [("org.eventb.core.label", "INITIALISATION")]
            [.action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "b ≔ 0")] []]
          , .event [("org.eventb.core.label", "step")]
            [.refinesEvent [("org.eventb.core.target", "step")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "b ≔ b + 1")] []]] }]

private def mergeProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "inv"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "left")]
          [.guard [("org.eventb.core.label", "g0"),
                   ("org.eventb.core.predicate", "x = 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ x")] []]
        , .event [("org.eventb.core.label", "right")]
          [.guard [("org.eventb.core.label", "g1"),
                   ("org.eventb.core.predicate", "x = 1")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ x")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .event [("org.eventb.core.label", "INITIALISATION")] []
          , .event [("org.eventb.core.label", "merge")]
            [.refinesEvent [("org.eventb.core.target", "left")] []
             , .refinesEvent [("org.eventb.core.target", "right")] []
             , .guard [("org.eventb.core.label", "g"),
                       ("org.eventb.core.predicate", "x = 0 ∨ x = 1")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ x")] []]] }]

private def nonEqualityWitnessProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "inv"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "step")]
          [.parameter [("org.eventb.core.identifier", "p")] []
           , .guard [("org.eventb.core.label", "g"),
                     ("org.eventb.core.predicate", "p > 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ p")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .event [("org.eventb.core.label", "INITIALISATION")] []
          , .event [("org.eventb.core.label", "step")]
            [.refinesEvent [("org.eventb.core.target", "step")] []
             , .parameter [("org.eventb.core.identifier", "q")] []
             , .guard [("org.eventb.core.label", "g"),
                       ("org.eventb.core.predicate", "q > 0")] []
             , .witness [("org.eventb.core.label", "p"),
                         ("org.eventb.core.predicate", "p > q")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ q")] []]] }]

private def extendedParameterProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "step")]
          [.parameter [("org.eventb.core.identifier", "p")] []
           , .guard [("org.eventb.core.label", "g"),
                     ("org.eventb.core.predicate", "p > 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ p")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .variable [("org.eventb.core.identifier", "y")] []
          , .event [("org.eventb.core.label", "INITIALISATION")] []
          , .event [("org.eventb.core.label", "step")]
            [.refinesEvent [("org.eventb.core.target", "step"),
                            ("org.eventb.core.extended", "true")] []
             , .action [("org.eventb.core.label", "set_y"),
                        ("org.eventb.core.assignment", "y ≔ p")] []]] }]

private def initializationRefinementProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "inv"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "x ≔ 0")] []]] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .variable [("org.eventb.core.identifier", "x")] []
          , .event [("org.eventb.core.label", "INITIALISATION")] []] }]

private def functionUpdateWdProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "f")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "f ∈ ℤ ⇸ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.action [("org.eventb.core.label", "empty"),
                    ("org.eventb.core.assignment", "f ≔ ∅")] []]
        , .event [("org.eventb.core.label", "step")]
          [.parameter [("org.eventb.core.identifier", "i")] []
           , .guard [("org.eventb.core.label", "domain"),
                     ("org.eventb.core.predicate", "i ∈ ℤ")] []
           , .action [("org.eventb.core.label", "update"),
                      ("org.eventb.core.assignment", "f(i) ≔ 1 ÷ i")] []]] }]

#guard match generateChecked checkedMissingProject "M" with
  | .error _ => true
  | .ok _ => false

#guard (generate defaultInitializationProject "M").any (fun obligation =>
  obligation.name == "INITIALISATION/__default_x/FIS")
#guard (generate defaultInitializationProject "M").any (fun obligation =>
  obligation.name == "INITIALISATION/inv/INV")
#guard match generateChecked defaultInitializationProject "M" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.name == "INITIALISATION/__default_x/FIS")
  | .error _ => false

#guard match generateChecked rightWitnessProject "B" with
  | .ok obligations =>
      obligations.any (fun obligation => obligation.name == "step/p/WFIS") &&
        obligations.any (fun obligation => obligation.name == "step/g/GRD" &&
          obligation.goal.map (fun goal =>
            let printed := Formula.print goal
            printed.contains "q + 1" && !printed.contains "p >") == some true) &&
        obligations.any (fun obligation => obligation.name == "step/set/SIM")
  | .error _ => false

#guard match generateChecked dataRefinementProject "B" with
  | .ok obligations =>
      !obligations.any (fun obligation => obligation.name == "step/set/SIM") &&
      obligations.any (fun obligation =>
          obligation.name == "step/glue/INV" &&
            obligation.goal.map (fun goal =>
              let printed := Formula.print goal
              !printed.contains "a + 1" && printed.contains "b + 1") == some true)
  | .error _ => false

#guard match generateChecked (rightWitnessProject ++ [hiddenParameterChild]) "C" with
  | .error _ => true
  | .ok _ => false

#guard match generateChecked mergeProject "B" with
  | .ok obligations =>
      obligations.any (fun obligation => obligation.name == "merge/MRG") &&
        obligations.any (fun obligation => obligation.name == "merge/set/SIM") &&
        obligations.all (fun obligation => !obligation.name.endsWith "/GRD")
  | .error _ => false

#guard match generateChecked nonEqualityWitnessProject "B" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.name == "step/p/WFIS" && obligation.goal.isSome)
  | .error _ => false

#guard match generateChecked extendedParameterProject "B" with
  | .ok _ => true
  | .error _ => false

#guard match generateChecked initializationRefinementProject "B" with
  | .ok obligations => obligations.all (fun obligation =>
      obligation.name != "INITIALISATION/set/SIM" ||
        !obligation.hyps.any (fun hypothesis =>
          hypothesis == .bin "=" (.id "x'") (.id "x")))
  | .error _ => false

#guard match generateChecked functionUpdateWdProject "M" with
  | .ok obligations => obligations.any (fun obligation =>
      obligation.name == "step/update/WD" &&
        obligation.goal.map (fun goal => !(Formula.print goal).contains "f(i) ⇒") == some true)
  | .error _ => false

#guard match locateWitness? Theory.empty rightWitnessProject "B" "step" "p" "WFIS" with
  | .ok (some (origin, obligation)) =>
      origin.witnessVariable == "p" &&
        (Formula.print origin.predicate).contains "q + 1" &&
        obligation.name == "step/p/WFIS"
  | _ => false

#guard match locateSim? Theory.empty rightWitnessProject "B" "step" "set" with
  | .ok (some (origin, obligation)) =>
      origin.abstractMachine == "A" &&
        origin.abstractAction.attr? "org.eventb.core.assignment" == some "x ≔ p" &&
        obligation.name == "step/set/SIM"
  | _ => false

#guard match locateSim? Theory.empty rightWitnessProject "B" "step" "missing" with
  | .ok none => true
  | _ => false

end EventB.POG
