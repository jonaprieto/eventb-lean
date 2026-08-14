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

/-- `target` is a workspace path such as `/Abstraction/M1_Landing_Sequence_Ctx`; only the
last segment names the component. -/
private def targetName (e : Elem) : Option String :=
  (attrOf e "target").map (fun t => (t.splitOn "/").getLast!)

private def eventParentName (ev : Elem) : Option String :=
  match (childrenOf ev "refinesEvent").filterMap targetName |>.head? with
  | some target => some target
  | none => if (attrOf ev "extended").getD "false" == "true" then some (labelOf ev) else none

private def inheritedEventParams (p : Project) : Nat → String → String → List String
  | 0, _, _ => []
  | depth + 1, machine, event =>
      match lookupComponent p machine with
      | none => []
      | some current =>
          match (childrenOf current.elem "event").find? (fun candidate =>
            labelOf candidate == event) with
          | none => []
          | some currentEvent =>
              match eventParentName currentEvent with
              | none => []
              | some parentEventName =>
                  match (childrenOf current.elem "refinesMachine").filterMap targetName |>.head? with
                  | none => []
                  | some parentName =>
                      match lookupComponent p parentName with
                      | none => []
                      | some parent =>
                          match (childrenOf parent.elem "event").find? (fun candidate =>
                            labelOf candidate == parentEventName) with
                          | none => []
                          | some parentEvent =>
                              let own := (childrenOf parentEvent "parameter").filterMap
                                (attrOf · "identifier")
                              own ++ inheritedEventParams p depth parentName parentEventName

/-- Contexts and machines a component depends on, deepest first, without repeats.

`visited` already stops repeats, so the recursion terminates on any well-formed project;
`depth` states the bound the type system cannot see. It is the number of components, so
a chain that reaches it has revisited one, meaning the dependency graph has a cycle. -/
def closureAux (p : Project) : Nat → List String → String → List String × List String
  | 0, visited, _ => (visited, [])
  | depth + 1, visited, name =>
    if visited.contains name then (visited, []) else
      match lookupComponent p name with
      | none => (name :: visited, [])
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
private def addComponent (p : Project) (c : Component) : M (List String) := do
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
  -- Each event's parameters are scoped to that event.
  for ev in childrenOf c.elem "event" do
    let ownParams := (childrenOf ev "parameter").filterMap (attrOf · "identifier")
    let inheritedParams := inheritedEventParams p p.length c.name (labelOf ev)
    let (eventErrors, bound) ← withEnvBindings do
      let mut eventErrors : List String := []
      -- A refining event's witnesses and predicates can mention the parameters of the
      -- abstract event. They are lexical inputs to this check, not project-global names.
      for name in inheritedParams do
        let st ← get
        match st.params.find? (fun pair => pair.1 == name) with
        | some (_, ty) => bind name ty
        | none => eventErrors := eventErrors ++
            [s!"unresolved abstract event parameter {name}"]
      for prm in childrenOf ev "parameter" do
        if let some n := attrOf prm "identifier" then bind n (← fresh)
      for g in childrenOf ev "guard" do
        if let some f := attrOf g "predicate" then
          eventErrors := eventErrors ++ (← runPredicate f)
      for act in childrenOf ev "action" do
        if let some f := attrOf act "assignment" then
          eventErrors := eventErrors ++ (← runPredicate f)
      for w in childrenOf ev "witness" do
        if let some f := attrOf w "predicate" then
          eventErrors := eventErrors ++ (← runPredicate f)
      return eventErrors
    errs := errs ++ eventErrors
    -- Parameters leave the environment so a later event cannot see them, but they are
    -- kept in `params` because the `.bpo` records their types alongside the variables.
    modify fun s =>
      { s with params := s.params ++ bound.filter (fun pair => ownParams.contains pair.1) }
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

/-- Infer every identifier type visible in `name`, as Rodin would record them. -/
def inferComponentIn (theory : Theory.Env) (p : Project) (name : String) :
    Except EventB.Error (List (String × Ty) × List String) :=
  let (_, order) := closure p [] name
  let roots := componentTheoryRoots p name
  let run : StateT St (Except String) (List (String × Ty) × List String) := do
    let mut errs : List String := []
    for dep in order do
      if let some c := lookupComponent p dep then
        errs := errs ++ (← addComponent p c)
    let st ← get
    let env := st.env ++ st.params
    let mut out : List (String × Ty) := []
    for (n, t) in env do
      if out.all (fun q => q.1 != n) then
        out := out ++ [(n, ← zonk t)]
    return (out, errs)
  match run.run' { theory, theoryRoots := roots } with
  | .ok result => .ok result
  | .error error => .error (EventB.Error.typing error)

def inferComponent (p : Project) (name : String) :
    Except EventB.Error (List (String × Ty) × List String) :=
  inferComponentIn Theory.empty p name

/-- Infer one expression against an already-built component environment. -/
private def inferTermAtText (theory : Theory.Env) (roots : List String) (env : List (String × Ty))
    (t : Term) : Except String Ty := do
  let (ty, st) ← (inferExpr t).run { env, theory, theoryRoots := roots }
  let (ty, _) ← (zonk ty).run st
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
