/-
Typing a whole component.

Nothing in a `.bum` states a type. Rodin derives every one of them from the axioms,
invariants and guards, and records the result in the `.bpo`. Reproducing those strings
therefore means reproducing the derivation, which is what makes P2 a real gate rather
than a file-format exercise.

A machine's environment is its whole closure: the contexts it sees (and everything they
extend), the machines it refines (and their contexts), then its own variables, then each
event's parameters. Constraints flow from every predicate in that closure, so an
invariant three refinements up is what pins a variable's type here.
-/

import EventB.Model
import EventB.Typing.Infer

namespace EventB.Typing

open EventB.Formula
open EventB.Prelude

/-- One component, keyed by the file name Rodin uses to refer to it. -/
structure Component where
  name : String
  elem : Elem
  /-- Native theories explicitly used by this component. -/
  theories : List String := []

abbrev Project := List Component

def lookupComponent (p : Project) (name : String) : Option Component :=
  List.find? (fun c => c.name == name) p

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

private def isExtended (ev : Elem) : Bool :=
  (attrOf ev "extended").getD "false" == "true" ||
    (childrenOf ev "refinesEvent").any
      (fun reference => (attrOf reference "extended").getD "false" == "true")

private def assignmentTargets (action : Elem) : List String :=
  match attrOf action "assignment" with
  | none => []
  | some source =>
      match Formula.parse source with
      | .error _ => []
      | .ok (.bin op lhs _) =>
          if op == "≔" then
            match lhs with
            | .app (.id functionName) _ => [functionName]
            | _ => Formula.flattenCommas lhs |>.filterMap fun term =>
                match term with
                | .id name => some name
                | .app (.id functionName) _ => some functionName
                | _ => none
          else if op == ":∈" || op == ":∣" then
            Formula.flattenCommas lhs |>.filterMap fun term =>
              match term with | .id name => some name | _ => none
          else []
      | .ok _ => []

private def assignmentShapeErrors (action : Elem) : List String :=
  match attrOf action "assignment" with
  | none => []
  | some source =>
      match Formula.parse source with
      | .ok (.bin op lhs rhs) =>
          let left := Formula.flattenCommas lhs
          let validDeterministic := left.all fun term =>
            match term with
            | .id _ | .app (.id _) _ => true
            | _ => false
          let validTargets := left.all fun term =>
            match term with | .id _ => true | _ => false
          if op == "≔" then
            (if left.length != (Formula.flattenCommas rhs).length then
                ["parallel assignment has different target and expression arity"] else []) ++
              (if validDeterministic then [] else
                ["assignment target is not an identifier or function application"])
          else if op == ":∈" || op == ":∣" then
            if validTargets then [] else ["nondeterministic assignment target is not an identifier"]
          else [s!"unsupported assignment operator {op}"]
      | .ok _ => ["assignment is not a binary Event-B assignment"]
      | .error error => [s!"assignment parse: {EventB.Error.render error}"]

private def duplicateNames (seen : List String) : List String → List String
  | [] => []
  | name :: rest =>
      if seen.contains name then name :: duplicateNames seen rest
      else duplicateNames (name :: seen) rest

private def rawInitializationActions (p : Project) : Nat → String → Elem → List Elem
  | 0, _, ev => childrenOf ev "action"
  | depth + 1, machine, ev =>
      let own := childrenOf ev "action"
      let inherited := eventTargets ev |>.flatMap fun target =>
        (lookupComponent p machine).toList.flatMap fun current =>
          (childrenOf current.elem "refinesMachine").filterMap targetName |>.flatMap
            fun parentName =>
            (lookupComponent p parentName).toList.flatMap fun parent =>
              (childrenOf parent.elem "event").find? (fun candidate => labelOf candidate == target)
                |>.toList.flatMap (rawInitializationActions p depth parentName)
      inherited ++ own

def initializationActions (p : Project) (c : Component) (ev : Elem) : List Elem :=
  let actions := childrenOf ev "action"
  if labelOf ev != "INITIALISATION" then actions
  else
    let assigned := rawInitializationActions p p.length c.name ev |>.flatMap assignmentTargets
    let variables := (childrenOf c.elem "variable").filterMap (attrOf · "identifier")
    actions ++ (variables.filter (fun v => !assigned.contains v)).map fun v =>
      .action [("org.eventb.core.label", "__default_" ++ v),
        ("org.eventb.core.assignment", v ++ " :∣ ⊤")] []

private def eventParameterNames (ev : Elem) : List String :=
  (childrenOf ev "parameter").filterMap (attrOf · "identifier")

private def validVariantType : Ty → Bool
  | .int => true
  | .pow (.mvar _) => false
  | .pow _ => true
  | _ => false

private def actionTexts (actions : List Elem) : List String :=
  actions.filterMap (attrOf · "assignment")

private def allEqual : List (List String) → Bool
  | [] => true
  | first :: rest => rest.all (· == first)

private def refinementCycle (p : Project) : Nat → List String → String → Bool
  | 0, _, _ => true
  | fuel + 1, seen, name =>
      if seen.contains name then true
      else
        match lookupComponent p name with
        | none => false
        | some component =>
            match (childrenOf component.elem "refinesMachine").filterMap targetName with
            | [] => false
            | [parent] => refinementCycle p fuel (name :: seen) parent
            | _ => false

private def dependencyCycle (p : Project) : Nat → List String → String → Bool
  | 0, _, _ => true
  | fuel + 1, seen, name =>
      if seen.contains name then true
      else
        match lookupComponent p name with
        | none => false
        | some component =>
            let dependencies :=
              (childrenOf component.elem "extendsContext" ++
                childrenOf component.elem "seesContext" ++
                childrenOf component.elem "refinesMachine").filterMap targetName
            dependencies.any (dependencyCycle p fuel (name :: seen))

private def effectiveEventActions (p : Project) : Nat → String → Elem → List Elem
  | 0, machine, ev =>
      match lookupComponent p machine with
      | some component => initializationActions p component ev
      | none => childrenOf ev "action"
  | depth + 1, machine, ev =>
      let own := match lookupComponent p machine with
        | some component => initializationActions p component ev
        | none => childrenOf ev "action"
      if !isExtended ev then own
      else
        let inherited := eventTargets ev |>.flatMap fun target =>
          (lookupComponent p machine).toList.flatMap fun current =>
            (childrenOf current.elem "refinesMachine").filterMap targetName |>.flatMap
              fun parentName =>
              (lookupComponent p parentName).toList.flatMap fun parent =>
                (childrenOf parent.elem "event").find?
                    (fun candidate => labelOf candidate == target)
                  |>.toList.flatMap (effectiveEventActions p depth parentName)
        own ++ inherited

private def componentReferenceErrors (p : Project) (c : Component) : List String :=
  let refs := childrenOf c.elem "extendsContext" ++ childrenOf c.elem "seesContext" ++
    childrenOf c.elem "refinesMachine"
  let componentErrors := (refs.filterMap targetName).filterMap fun target =>
    if lookupComponent p target |>.isSome then none
    else some s!"unresolved component reference {target} from {c.name}"
  let parentNames := (childrenOf c.elem "refinesMachine").filterMap targetName
  let variableNames := (childrenOf c.elem "variable").filterMap (attrOf · "identifier")
  let constantNames := (childrenOf c.elem "constant").filterMap (attrOf · "identifier")
  let setNames := (childrenOf c.elem "carrierSet").filterMap (attrOf · "identifier")
  let namespaceNames := constantNames ++ setNames
  let namespaceErrors :=
    (duplicateNames [] variableNames).map (fun name =>
      s!"duplicate variable declaration {name} in {c.name}") ++
    variableNames.filter (fun name => namespaceNames.contains name) |>.map (fun name =>
      s!"variable {name} in {c.name} collides with a constant or carrier set")
  let eventNamespaceErrors := (childrenOf c.elem "event").flatMap fun ev =>
    let params := eventParameterNames ev
    (duplicateNames [] params).map (fun name =>
      s!"duplicate event parameter {name} in {c.name}/{labelOf ev}") ++
    params.filter (fun name => variableNames.contains name || namespaceNames.contains name)
      |>.map (fun name =>
        s!"event parameter {name} in {c.name}/{labelOf ev} collides with a declaration")
  let initializationErrors :=
    if c.elem.tag == "org.eventb.core.machineFile" then
      let count := (childrenOf c.elem "event").countP (fun ev => labelOf ev == "INITIALISATION")
      if count == 1 then [] else
        [s!"machine {c.name} must have exactly one INITIALISATION event"]
    else []
  let graphErrors :=
    (if parentNames.length > 1 then
       [s!"component {c.name} has multiple refinement parents"] else []) ++
    (if refinementCycle p (p.length + 1) [] c.name then
       [s!"refinement cycle reaches {c.name}"] else [])
    ++ (if dependencyCycle p (p.length + 1) [] c.name then
       [s!"component dependency cycle reaches {c.name}"] else [])
  let eventErrors := childrenOf c.elem "event" |>.flatMap fun ev =>
    (childrenOf ev "refinesEvent").filterMap targetName |>.flatMap fun target =>
      if parentNames.any fun parentName =>
          match lookupComponent p parentName with
          | none => false
          | some parent => (childrenOf parent.elem "event").any
              (fun candidate => labelOf candidate == target) then []
      else [s!"unresolved event reference {target} from {c.name}/{labelOf ev}"]
  let convergenceErrors := childrenOf c.elem "event" |>.flatMap fun ev =>
    (childrenOf ev "refinesEvent").filterMap targetName |>.flatMap fun target =>
      parentNames.flatMap fun parentName =>
        match lookupComponent p parentName with
        | none => []
        | some parent =>
            match (childrenOf parent.elem "event").find?
                (fun candidate => labelOf candidate == target) with
            | some abstractEvent =>
                if (attrOf abstractEvent "convergence").getD "0" == "2" &&
                    (attrOf ev "convergence").getD "0" == "0" then
                  [s!"ordinary event {c.name}/{labelOf ev} cannot refine anticipated " ++
                    s!"event {target}"]
                else []
            | none => []
  let mergeErrors := childrenOf c.elem "event" |>.flatMap fun ev =>
    let refs := (childrenOf ev "refinesEvent").filterMap targetName
    if refs.length <= 1 then []
    else
      match parentNames.head?.bind (lookupComponent p ·) with
      | none => []
      | some parent =>
          let abstractEvents := refs.filterMap fun target =>
            (childrenOf parent.elem "event").find? (fun candidate => labelOf candidate == target)
          if abstractEvents.length != refs.length then []
          else
            let mergePrefix := s!"merged event {c.name}/{labelOf ev}"
            (if allEqual (abstractEvents.map (fun abstractEvent =>
                actionTexts (effectiveEventActions p p.length parent.name abstractEvent))) then []
             else [mergePrefix ++ " refines abstract events with different actions"]) ++
            (if allEqual (abstractEvents.map eventParameterNames) then []
             else [mergePrefix ++ " refines abstract events with different parameters"])
  componentErrors ++ namespaceErrors ++ eventNamespaceErrors ++ initializationErrors ++
    graphErrors ++ eventErrors ++ convergenceErrors ++ mergeErrors

private def theoryReferenceErrors (theory : Theory.Env) (roots : List String) : List String :=
  let rec visit (fuel : Nat) (seen : List String) (name : String) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        if seen.contains name then []
        else match Theory.lookupTheory? theory name with
          | none => [s!"unresolved theory reference {name}"]
          | some spec => spec.imports.flatMap (visit fuel (name :: seen))
  roots.flatMap (visit (theory.theories.length + roots.length + 1) [])

private def eventParamBindings
    (records : List ((String × String) × List (String × Ty)))
    (component event : String) : List (String × Ty) :=
  (records.find? (fun record => record.1.1 == component && record.1.2 == event)).map
    (·.2) |>.getD []

private def dedupBindings (seen : List String) : List (String × Ty) → List (String × Ty)
  | [] => []
  | binding :: rest =>
      if seen.contains binding.1 then dedupBindings seen rest
      else binding :: dedupBindings (binding.1 :: seen) rest

private def inheritedEventBindings
    (p : Project) (records : List ((String × String) × List (String × Ty))) :
    Nat → String → String → List (String × Ty)
  | 0, _, _ => []
  | depth + 1, machine, event =>
      match lookupComponent p machine with
      | none => []
      | some current =>
          match (childrenOf current.elem "event").find? (fun candidate =>
            labelOf candidate == event) with
          | none => []
          | some currentEvent =>
              let targets := eventTargets currentEvent
              let parents := (childrenOf current.elem "refinesMachine").filterMap targetName
              let collected := parents.flatMap fun parentName =>
                match lookupComponent p parentName with
                | none => []
                | some parent =>
                    targets.flatMap fun parentEventName =>
                      if (childrenOf parent.elem "event").any (fun candidate =>
                          labelOf candidate == parentEventName) then
                        eventParamBindings records parentName parentEventName ++
                          inheritedEventBindings p records depth parentName parentEventName
                      else []
              dedupBindings [] collected

def visibleEventBindings
    (p : Project) (records : List ((String × String) × List (String × Ty)))
    (component event : String) : List (String × Ty) :=
  eventParamBindings records component event ++
    inheritedEventBindings p records p.length component event

/-- Contexts and machines a component depends on, deepest first, without repeats.

`visited` already stops repeats, so the recursion terminates on any well-formed project;
`depth` states the bound the type system cannot see. It is the number of components, so
a chain that reaches it has revisited one, meaning the dependency graph has a cycle. -/
def closureAux (p : Project) : Nat → List String → String → List String × List String
  | 0, visited, _ => (visited, [])
  | depth + 1, visited, name =>
      if visited.contains name then (visited, []) else
      match lookupComponent p name with
      | none => (name :: visited, [name])
      | some c =>
        let deps :=
          (childrenOf c.elem "extendsContext" ++ childrenOf c.elem "seesContext"
            ++ childrenOf c.elem "refinesMachine").filterMap targetName
        let (visited, ordered) :=
          deps.foldl
            (fun (acc : List String × List String) d =>
              let (v, o) := closureAux p depth acc.1 d
              (v, acc.2 ++ o))
            (name :: visited, [])
        (visited, ordered ++ [name])

def closure (p : Project) (visited : List String) (name : String) :
    List String × List String :=
  closureAux p p.length visited name

def componentTheoryRoots (p : Project) (name : String) : List String :=
  let (_, order) := closure p [] name
  order.flatMap fun dep =>
    (lookupComponent p dep).map (·.theories) |>.getD []

/-- Declare the identifiers a component introduces, then feed every predicate it states
to the checker. Errors are collected rather than thrown: one unsupported guard should
cost that guard's constraints, not the whole file's types. -/
private def addComponentMode (strict : Bool) (p : Project) (c : Component) : M (List String) := do
  let mut errs : List String := []
  -- Carrier sets and constants first, so axioms can refer to them in any order.
  for s in childrenOf c.elem "carrierSet" do
    if let some n := attrOf s "identifier" then declare n (.pow (.given n))
  for k in childrenOf c.elem "constant" do
    if let some n := attrOf k "identifier" then declare n (← fresh)
  for v in childrenOf c.elem "variable" do
    if let some n := attrOf v "identifier" then do
      let t ← freshFor n
      -- A refinement redeclares the variables it keeps. Rebinding them would throw away
      -- the type the abstract machine's invariants already pinned down.
      declare n t
      -- Rodin puts the after-state `v'` in scope with the same type as `v`, and the
      -- `.bpo` records it, so an action assigning to `v` types both.
      declare (n ++ "'") t
  let predicates := childrenOf c.elem "axiom" ++ childrenOf c.elem "invariant"
  for a in predicates do
    if let some f := attrOf a "predicate" then
      errs := errs ++ (← runPredicate f)
  for variant in childrenOf c.elem "variant" do
    if let some f := attrOf variant "expression" then
      errs := errs ++ (← runExpression f)
  let hasConvergent := (childrenOf c.elem "event").any
    (fun event => (attrOf event "convergence").getD "0" == "1")
  if hasConvergent && (childrenOf c.elem "variant").isEmpty then
    errs := errs ++ [s!"convergent event in {c.name} requires an explicit variant"]
  -- Each event's parameters are scoped to that event.
  for ev in childrenOf c.elem "event" do
    let ownParams := (childrenOf ev "parameter").filterMap (attrOf · "identifier")
    let records := (← get).eventParams
    let actionTargets := effectiveEventActions p p.length c.name ev |>.flatMap assignmentTargets
    let ownActionTargets := initializationActions p c ev |>.flatMap assignmentTargets
    let variables := (childrenOf c.elem "variable").filterMap (attrOf · "identifier")
    errs := errs ++ (initializationActions p c ev).flatMap assignmentShapeErrors |>.map fun error =>
      s!"{error} in {c.name}/{labelOf ev}"
    errs := errs ++
      (ownActionTargets.filter (fun target => !variables.contains target)).map fun target =>
      s!"assignment target {target} is not a variable in {c.name}/{labelOf ev}"
    errs := errs ++ (duplicateNames [] actionTargets).map fun target =>
      s!"duplicate assignment target {target} in {c.name}/{labelOf ev}"
    let inheritedParams := inheritedEventBindings p records p.length c.name (labelOf ev)
    let parentNames := (childrenOf c.elem "refinesMachine").filterMap targetName
    let mergedRefs := (childrenOf ev "refinesEvent").filterMap targetName
    if labelOf ev == "INITIALISATION" then
      if !ownParams.isEmpty then
        errs := errs ++ [s!"INITIALISATION in {c.name} must not declare parameters"]
      if !(childrenOf ev "guard").isEmpty then
        errs := errs ++ [s!"INITIALISATION in {c.name} must not declare guards"]
    if mergedRefs.length > 1 then
      match parentNames.head? with
      | some parentName =>
          let signatures ← mergedRefs.mapM fun target => do
            (eventParamBindings records parentName target).mapM fun (n, t) => do
              let t ← zonk t
              pure (n ++ ":" ++ t.print)
          if !allEqual signatures then
            errs := errs ++
              [s!"merged event {c.name}/{labelOf ev} refines abstract events with " ++
                "different parameter types"]
      | none => pure ()
    let (eventErrors, bound) ← withEnvBindings do
      let mut eventErrors : List String := []
      -- Compatibility inference mirrors the pinned corpus. Strict inference keeps
      -- abstract parameters available only while checking witness predicates.
      if !strict then
        for (name, ty) in inheritedParams do bind name ty
      for prm in childrenOf ev "parameter" do
        if let some n := attrOf prm "identifier" then bind n (← fresh)
      for g in childrenOf ev "guard" do
        if let some f := attrOf g "predicate" then
          eventErrors := eventErrors ++ (← runPredicate f)
      for act in initializationActions p c ev do
        if let some f := attrOf act "assignment" then
          eventErrors := eventErrors ++ (← runPredicate f)
      if strict then
        let witnessErrors ← withEnv do
          for (name, ty) in inheritedParams do bind name ty
          let mut errors : List String := []
          for w in childrenOf ev "witness" do
            if let some f := attrOf w "predicate" then
              errors := errors ++ (← runPredicate f)
          return errors
        eventErrors := eventErrors ++ witnessErrors
      else
        for w in childrenOf ev "witness" do
          if let some f := attrOf w "predicate" then
            eventErrors := eventErrors ++ (← runPredicate f)
      return eventErrors
    errs := errs ++ eventErrors
    -- Parameters leave the environment so a later event cannot see them, but they are
    -- kept in `params` because the `.bpo` records their types alongside the variables.
    let ownBound := bound.filter (fun pair => ownParams.contains pair.1)
    modify fun s =>
      { s with
          params := s.params ++ ownBound
          eventParams := s.eventParams ++ [((c.name, labelOf ev), ownBound)] }
  return errs
where
  /-- Reuse the existing type if the name is already declared, so a refinement does not
  discard what the abstract machine established. -/
  freshFor (n : String) : M Ty := do
    match ← lookup? n with
    | some t => return t
    | none => fresh
  declare (n : String) (t : Ty) : M Unit := do
    match ← lookup? n with
    | some _ => return ()
    | none => bind n t
  runPredicate (f : String) : M (List String) := do
    match Formula.parse f with
    | .error e => return [s!"parse: {EventB.Error.render e}"]
    | .ok term =>
      let st ← get
      match (checkPred term).run st with
      | .ok (_, st') => set st'; return []
      -- Keep the pre-error state: a half-applied unification is worse than none.
      | .error e => return [s!"{e}"]

  runExpression (f : String) : M (List String) := do
    match Formula.parse f with
    | .error e => return [s!"parse: {EventB.Error.render e}"]
    | .ok term =>
      let st ← get
      match (inferExpr term).run st with
      | .ok (ty, st') =>
          match (zonk ty).run st' with
          | .ok (zoned, st'') =>
              set st''
              if validVariantType zoned then return []
              else return ["variant expression must have integer or set type"]
          | .error e => return [s!"{e}"]
      | .error e => return [s!"{e}"]

structure ComponentInference where
  types : List (String × Ty)
  eventParams : List ((String × String) × List (String × Ty))
  diagnostics : List String

private def containsMVar : Ty → Bool
  | .mvar _ => true
  | .given _ | .int | .bool => false
  | .pow t => containsMVar t
  | .prod a b => containsMVar a || containsMVar b

/-- Infer every identifier type visible in `name`, retaining event-local bindings for
POG consumers that must resolve repeated parameter names by lexical scope. -/
private def inferComponentDetailsModeIn (strict : Bool) (theory : Theory.Env) (p : Project)
    (name : String) :
    Except EventB.Error ComponentInference :=
  let (_, order) := closure p [] name
  let roots := componentTheoryRoots p name
  let run : StateT St (Except String) ComponentInference := do
    let mut errs : List String := theoryReferenceErrors theory roots
    for dep in order do
      if let some c := lookupComponent p dep then
        errs := errs ++ componentReferenceErrors p c ++ (← addComponentMode strict p c)
      else
        errs := errs ++ [s!"unresolved component reference {dep}"]
    let st ← get
    let env := st.env ++ st.params
    let mut out : List (String × Ty) := []
    for (n, t) in env do
      if out.all (fun q => q.1 != n) then
        let t ← zonk t
        if containsMVar t then
          errs := errs ++ [s!"unresolved type for {n} in {name}"]
        else
          out := out ++ [(n, t)]
    let eventParams ← st.eventParams.mapM fun (key, bindings) => do
      let bindings ← bindings.mapM fun (n, t) => do
        let t ← zonk t
        if containsMVar t then
          throw s!"unresolved type for event parameter {n} in {key.1}/{key.2}"
        pure (n, t)
      pure (key, bindings)
    return { types := out, eventParams, diagnostics := errs }
  match run.run' { theory, theoryRoots := roots } with
  | .ok result => .ok result
  | .error error => .error (EventB.Error.typing error)

def inferComponentDetailsIn (theory : Theory.Env) (p : Project) (name : String) :
    Except EventB.Error ComponentInference :=
  inferComponentDetailsModeIn false theory p name

def inferComponentDetailsCheckedIn (theory : Theory.Env) (p : Project) (name : String) :
    Except EventB.Error ComponentInference :=
  inferComponentDetailsModeIn true theory p name

def inferComponentIn (theory : Theory.Env) (p : Project) (name : String) :
    Except EventB.Error (List (String × Ty) × List String) :=
  (inferComponentDetailsIn theory p name).map fun result =>
    (result.types, result.diagnostics)

def inferComponent (p : Project) (name : String) :
    Except EventB.Error (List (String × Ty) × List String) :=
  inferComponentIn Theory.empty p name

private def missingReferenceProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.seesContext [("org.eventb.core.target", "Missing")] []]
     theories := ["MissingTheory"] }]

#guard match inferComponent missingReferenceProject "M" with
  | .ok (_, errors) =>
      errors.contains "unresolved component reference Missing from M" &&
        errors.contains "unresolved theory reference MissingTheory"
  | .error _ => false

private def cyclicRefinementProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.refinesMachine [("org.eventb.core.target", "B")] []] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [.refinesMachine [("org.eventb.core.target", "A")] []] }]

#guard match inferComponent cyclicRefinementProject "A" with
  | .ok (_, errors) => errors.any (fun error => error.contains "refinement cycle")
  | .error _ => false

private def multipleParentProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")] [] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")] [] }
   , { name := "C"
       elem := .machineFile [("org.eventb.core.name", "C")]
         [.refinesMachine [("org.eventb.core.target", "A")] []
          , .refinesMachine [("org.eventb.core.target", "B")] []] }]

#guard match inferComponent multipleParentProject "C" with
  | .ok (_, errors) => errors.any (fun error => error.contains "multiple refinement parents")
  | .error _ => false

private def contextCycleProject : Project :=
  [{ name := "C1"
     elem := .contextFile [("org.eventb.core.name", "C1")]
       [.extendsContext [("org.eventb.core.target", "C2")] []] }
   , { name := "C2"
       elem := .contextFile [("org.eventb.core.name", "C2")]
         [.extendsContext [("org.eventb.core.target", "C1")] []] }
   , { name := "M"
       elem := .machineFile [("org.eventb.core.name", "M")]
         [.seesContext [("org.eventb.core.target", "C1")] []] }]

#guard match inferComponent contextCycleProject "M" with
  | .ok (_, errors) => errors.any (fun error => error.contains "dependency cycle")
  | .error _ => false

private def initializationGuardProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .event [("org.eventb.core.label", "INITIALISATION")]
          [.guard [("org.eventb.core.label", "bad"),
                   ("org.eventb.core.predicate", "x = 0")] []]] }]

#guard match inferComponent initializationGuardProject "M" with
  | .ok (_, errors) => errors.any (fun error => error.contains "must not declare guards")
  | .error _ => false

private def duplicateInitializationProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []] }]

#guard match inferComponent duplicateInitializationProject "M" with
  | .ok (_, errors) => errors.any (fun error => error.contains "exactly one INITIALISATION")
  | .error _ => false

private def invalidVariantProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "b")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "b ∈ BOOL")] []
        , .variant [("org.eventb.core.expression", "b")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []] }]

#guard match inferComponent invalidVariantProject "M" with
  | .ok (_, errors) => errors.any (fun error => error.contains "variant expression")
  | .error _ => false

private def primedBinderProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "choose")]
          [.action [("org.eventb.core.label", "set"),
                    ("org.eventb.core.assignment", "x :∣ ∀y' · y' = x'")] []]
        , .event [("org.eventb.core.label", "INITIALISATION")] []] }]

#guard match inferComponent primedBinderProject "M" with
  | .ok (_, errors) => errors.isEmpty
  | .error _ => false

private def strictScopeProject : Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
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
             , .guard [("org.eventb.core.label", "bad"),
                       ("org.eventb.core.predicate", "p > 0")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ x")] []]] }]

#guard match inferComponentDetailsCheckedIn Theory.empty strictScopeProject "B" with
  | .ok details => details.diagnostics.any (fun error => error.contains "unbound identifier p")
  | .error _ => false

private def duplicateAssignmentProject : Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .event [("org.eventb.core.label", "e")]
          [.action [("org.eventb.core.label", "a1"),
                    ("org.eventb.core.assignment", "x ≔ 0")] []
           , .action [("org.eventb.core.label", "a2"),
                      ("org.eventb.core.assignment", "x ≔ 1")] []]
       ] }]

#guard match inferComponent duplicateAssignmentProject "M" with
  | .ok (_, errors) => errors.any (fun error => error.contains "duplicate assignment target x")
  | .error _ => false

/-- Infer one expression against an already-built component environment. -/
private def inferTermAtText (theory : Theory.Env) (roots : List String) (env : List (String × Ty))
    (t : Term) : Except String Ty := do
  let (ty, st) ← (inferExpr t).run { env, theory, theoryRoots := roots }
  let (ty, _) ← (zonk ty).run st
  if containsMVar ty then
    throw "unresolved type metavariable"
  return ty

def inferTermAt (theory : Theory.Env) (roots : List String) (env : List (String × Ty))
    (t : Term) : Except EventB.Error Ty :=
  (inferTermAtText theory roots env t).mapError EventB.Error.typing

def inferTermIn (theory : Theory.Env) (env : List (String × Ty)) (t : Term) :
    Except EventB.Error Ty := do
  let roots := theory.theories.map (·.name)
  inferTermAt theory roots env t

def inferTerm (env : List (String × Ty)) (t : Term) : Except EventB.Error Ty :=
  inferTermIn Theory.empty env t

/-! Self-checks. The corpus pins the common cases; these pin the shapes it happens not
to contain, and the printer conventions the `.bpo` comparison depends on. -/

#guard match (withEnvBindings (bind "x" .int)).run {} with
  | .ok ((_, [ ("x", .int) ]), state) => state.env.isEmpty
  | _ => false

#guard match inferTerm [] (.set []) with
  | .error error => error.message.contains "unresolved type metavariable"
  | .ok _ => false

/-- `given` are identifiers with a known type, `unknown` are the ones inference has to
work out. Metavariables must come from `fresh` so the substitution has a slot for them. -/
private def inferOne (given : List (String × Ty)) (unknown : List String)
    (pred name : String) : Option String :=
  match Formula.parse pred with
  | .error _ => none
  | .ok term =>
    let run : StateT St (Except String) (Option String) := do
      given.forM (fun (n, t) => bind n t)
      unknown.forM (fun n => do bind n (← fresh))
      checkPred term
      match ← lookup? name with
      | some t => return some (← zonk t).print
      | none => return none
    match run.run' {} with
    | .ok r => r
    | .error _ => none

-- `x ⊆ S` makes `x` a set of whatever `S` holds.
#guard inferOne [("S", .pow (.given "T"))] ["x"] "x ⊆ S" "x" == some "ℙ(T)"
-- Function application constrains both the function and its argument.
#guard inferOne [("n", .int)] ["f"] "f(n) = TRUE" "f" == some "ℙ(ℤ×BOOL)"
-- An arrow builds a set of relations, so membership in it types the relation itself.
#guard inferOne [("S", .pow (.given "T"))] ["r"] "r ∈ S ⇸ S" "r"
  == some "ℙ(T×T)"
-- A maplet inside a set extension propagates through both components.
#guard inferOne [("n", .int)] ["r"] "r = {n ↦ TRUE}" "r" == some "ℙ(ℤ×BOOL)"
#guard inferOne [("x", .int), ("y", .bool)] ["a", "b"] "a,b ≔ x,y" "a" == some "ℤ"
#guard inferOne [("S", .pow .int), ("m", .int), ("t", .bool)] ["f"]
  "f = f  (S × {m ↦ t})" "f" == some "ℙ(ℤ×(ℤ×BOOL))"
-- `dom` and relational image agree on the relation's shape.
#guard (inferOne [("S", .pow .int)] ["r"] "dom(r) = S" "r").isSome
-- Products print left-nested without brackets and right-nested with them, as Rodin does.
#guard (Ty.pow (.prod (.prod .int .int) .int)).print == "ℙ(ℤ×ℤ×ℤ)"
#guard (Ty.pow (.prod .int (.prod .int .int))).print == "ℙ(ℤ×(ℤ×ℤ))"
-- Every type Rodin writes parses back to the tree that prints it.
#guard (Ty.parse "ℙ(AIRPLANES×ℤ)").map Ty.print == some "ℙ(AIRPLANES×ℤ)"
#guard (Ty.parse "ℙ(ℤ×ℤ×ℤ)").map Ty.print == some "ℙ(ℤ×ℤ×ℤ)"
#guard (Ty.parse "BOOL").map Ty.print == some "BOOL"
-- A type error is a type error: an integer is not a set of trains.
#guard inferOne [("S", .pow (.given "TRAIN")), ("n", .int)] [] "n = S" "n" == none

-- A becomes-such-that action checks both before and primed after-state names.
#guard inferOne [("x", .int), ("x'", .int), ("y", .int), ("y'", .int)] []
    "x, y :∣ x' = y' ∧ y' = x' + 1" "x" == some "ℤ"

private def demoTheory : Theory.Env :=
  match Theory.add Theory.empty
      { name := "Demo", symbols :=
        [{ name := "LIMIT", kind := .constant, type := some .int
           description := "A demo theory constant.",
           id := SymbolId.unqualified "LIMIT", source := SourceRange.synthetic }] } with
  | .ok env => env
  | .error _ => Theory.empty

#guard match inferTermIn demoTheory [] (.id "LIMIT") with
  | .ok .int => true
  | _ => false
#guard match inferTermAt demoTheory [] [] (.id "LIMIT") with
  | .error _ => true
  | _ => false

end EventB.Typing
