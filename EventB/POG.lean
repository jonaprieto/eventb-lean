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
  deriving BEq, Repr, Inhabited

def Obligation.canonical (obligation : Obligation) : String :=
  String.intercalate "\n"
    ["component=" ++ obligation.component
    , "name=" ++ obligation.name
    , "kind=" ++ obligation.kind
    , "theories=" ++ String.intercalate "," obligation.theoryRoots
    , "hyps=" ++ String.intercalate "\n" (obligation.hyps.map Formula.print)
    , "goal=" ++ (obligation.goal.map Formula.print |>.getD "<pending>")]

private def childrenOf (e : Elem) (tag : String) : List Elem :=
  e.children.filter (fun c => c.tag == "org.eventb.core." ++ tag)

private def attrOf (e : Elem) (key : String) : Option String :=
  e.attr? ("org.eventb.core." ++ key)

private def labelOf (e : Elem) : String := (attrOf e "label").getD ""

private def targetName (e : Elem) : Option String :=
  (attrOf e "target").map (fun t => (t.splitOn "/").getLast!)

/-- Identifiers occurring in a formula. Binders are not subtracted: an invariant that
quantifies over a name shadowing a variable would over-report, which the corpus does not
contain, and over-reporting here only ever adds an obligation Rodin also has. -/
def identifiers : Term → List String
  | .id n => [n]
  | .num _ => []
  | .bin _ a b => identifiers a ++ identifiers b
  | .pre _ a | .post _ a => identifiers a
  | .app f a => identifiers f ++ identifiers a
  | .img r a => identifiers r ++ identifiers a
  | .set ts => ts.flatMap identifiers
  | .bind _ p b => identifiers p ++ identifiers b

private def freeOf (formula : String) : List String :=
  match Formula.parse formula with
  | .ok t => identifiers t
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
    | .ok (.bin "≔" (.app (.id f) x) rhs) =>
        [(f, .bin "" (.id f) (.set [.bin "↦" x rhs]))]
    | .ok (.bin "≔" lhs rhs) =>
        match Formula.flattenCommas lhs, Formula.flattenCommas rhs with
        | [.id v], [e] => [(v, e)]
        -- `v, w ≔ E, F` assigns componentwise.
        | vs, es => (vs.zip es).filterMap fun (v, e) =>
            match v with | .id n => some (n, e) | _ => none
    | _ => []

/-- The variables an action assigns. Rodin's three assignment forms all name their
targets on the left: `v ≔ E`, `v :∈ S`, and `v, w :∣ P`. -/
private def assignedBy (action : Elem) : List String :=
  match attrOf action "assignment" with
  | none => []
  | some a =>
    match Formula.parse a with
    | .error _ => []
    | .ok (.bin op lhs _) =>
        if op == "≔" || op == ":∈" || op == ":∣" then Formula.flattenCommas lhs
          |>.flatMap identifiers
        else []
    | .ok _ => []

private def targetEventName (ev : Elem) : String :=
  ((childrenOf ev "refinesEvent").filterMap targetName).head?.getD (labelOf ev)

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
    if (attrOf ev "extended").getD "false" != "true" then own else
      match lookupComponent p machine with
      | none => own
      | some m =>
        let abstract := (childrenOf m.elem "refinesMachine").filterMap targetName
        let inherited := abstract.flatMap fun am =>
          match lookupComponent p am with
          | none => []
          | some a =>
            match (childrenOf a.elem "event").find? (fun e =>
              labelOf e == targetEventName ev) with
            | none => []
            | some ae => inheritedChildren p tag depth am ae
        inherited ++ own

def effectiveActions (p : Project) (machine : String) (ev : Elem) : List Elem :=
  inheritedChildren p "action" p.length machine ev

def effectiveGuards (p : Project) (machine : String) (ev : Elem) : List Elem :=
  inheritedChildren p "guard" p.length machine ev

/-- The substitution an event performs, including what the abstract machine still does
to variables the concrete event does not touch.

A gluing invariant mentions abstract variables, and those keep evolving under the
abstract event even when the refinement never names them, so `scheduledAirplanes =
dom(landing_sequence)` becomes `∅ = dom(∅)` under an INITIALISATION that only assigns
`landing_sequence` here and leaves the other to the machine above. Concrete assignments
win; `depth` bounds the walk by the component count, as elsewhere. -/
def eventSubst (p : Project) : Nat → String → Elem → List (String × Term)
  | 0, _, ev => (childrenOf ev "action").flatMap substOf
  | depth + 1, machine, ev =>
    let own := (childrenOf ev "action").flatMap substOf
    let inherited :=
      match lookupComponent p machine with
      | none => []
      | some m =>
        ((childrenOf m.elem "refinesMachine").filterMap targetName).flatMap fun am =>
          match lookupComponent p am with
          | none => []
          | some a =>
            let target := targetEventName ev
            match (childrenOf a.elem "event").find? (fun e => labelOf e == target) with
            | none => []
            | some ae => eventSubst p depth am ae
    own ++ inherited.filter (fun q => !own.any (fun o => o.1 == q.1))

/-- Guards and actions of the abstract event a refined event refines. These are what GRD
and SIM obligations are named after: the abstract label, not the concrete one. -/
private def abstractEvent (p : Project) (machine : String) (ev : Elem) :
    Option (String × Elem) := do
  let m ← lookupComponent p machine
  let am ← ((childrenOf m.elem "refinesMachine").filterMap targetName).head?
  let a ← lookupComponent p am
  let target ← if labelOf ev == "INITIALISATION" then some "INITIALISATION"
    else ((childrenOf ev "refinesEvent").filterMap targetName).head?
  let ae ← (childrenOf a.elem "event").find? (fun e => labelOf e == target)
  return (am, ae)

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

private def wdFunctionType (context : WdContext) (f : Term) : Option Term :=
  match inferTermAt context.theory context.roots context.env f with
  | .ok (.pow (.prod a b)) => some (.bin "⇸" (wdType a) (wdType b))
  | _ => none

private def wdNonempty (s : Term) : Term := .bin "≠" s (.set [])

private def wdBound (isMax : Bool) (s : Term) : Term :=
  let b := .id (if (identifiers s).contains "b" then "b0" else "b")
  let x := .id (if (identifiers s).contains "x" then "x0" else "x")
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
      op == "÷" || op == "mod" || needsWD totalKeywords a || needsWD totalKeywords b
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

private def wdGoal (theory : Theory.Env) (roots totalKeywords : List String)
    (env : List (String × Ty)) (formula : String) : Option Term :=
  match Formula.parse formula with
  | .ok t => wdTerm theory roots totalKeywords env t
  | .error _ => none

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
def generateIn (theory : Theory.Env) (p : Project) (name : String) : List Obligation := Id.run do
  match lookupComponent p name with
  | none => return []
  | some c =>
    let isMachine := c.elem.tag == "org.eventb.core.machineFile"
    let roots := componentTheoryRoots p name
    let finalize := fun obligations : List Obligation => obligations.map fun obligation =>
      { obligation with
          component := name
          theoryRoots := roots
          goal := obligation.goal.map (Theory.normalize theory roots)
          hyps := obligation.hyps.map (Theory.normalize theory roots) }
    let total := totalKeywords theory roots
    let types := match inferComponentIn theory p name with
      | .ok (env, _) => env
      | .error _ => []
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
    let invariants := childrenOf c.elem "invariant"
    for ev in childrenOf c.elem "event" do
      let base := if labelOf ev == "INITIALISATION" then contextAxioms p name
        else contextHyps p name
      let actions := effectiveActions p name ev
      let witnesses := (childrenOf ev "witness").filterMap fun w =>
        match Formula.parse ((attrOf w "predicate").getD "") with
        | .ok (.bin "=" (.id v) e) => some (v, e)
        | _ => none
      -- A non-extended refined event still executes its abstract actions.  Use the
      -- refinement substitution here so inherited assignments trigger preservation
      -- obligations for concrete invariants as well as for the after-state formula.
      let assigned := (eventSubst p p.length name ev).map (·.1)
      -- An invariant needs re-proving only if the event can change something it
      -- mentions. This filter is what keeps the INV count at Rodin's 934 rather than
      -- events times invariants.
      for inv in invariants do
        if (attrOf inv "theorem").getD "false" != "true" then
          let free := freeOf ((attrOf inv "predicate").getD "")
          if assigned.any (fun v => free.contains v) then
            -- The obligation is the invariant restated over the after-state, which is
            -- exactly the invariant with the event's assignments substituted in.
            let σ := eventSubst p p.length name ev
            let goal := (Formula.parse ((attrOf inv "predicate").getD "")).toOption.map
              (fun predicate => Formula.subst witnesses (Formula.subst σ predicate))
            -- The event's guards hold when it fires, so they join the standing
            -- hypotheses.
            let guards := (effectiveGuards p name ev).filterMap fun g =>
              (Formula.parse ((attrOf g "predicate").getD "")).toOption
            out := out ++
              [{ name := labelOf ev ++ "/" ++ labelOf inv ++ "/INV", kind := "INV",
                 goal := goal, hyps := base ++ guards }]
            -- The invariant is re-stated over the after-state, so if it was
            -- conditionally defined before, the substituted form needs its own WD.
            if wdRequired total ((attrOf inv "predicate").getD "") then
              out := out ++
                [{ name := labelOf ev ++ "/" ++ labelOf inv ++ "/WD", kind := "WD",
                   goal := wdGoal theory roots total types
                     ((attrOf inv "predicate").getD "") }]
      -- Refinement obligations are named after the abstract event's labels.
      if let some (am, ae) := abstractEvent p name ev then
        if (attrOf ev "extended").getD "false" != "true" then
          -- Guard strengthening: the concrete event must be enabled only where the
          -- abstract one is, so the goal is the abstract guard itself. A witness names
          -- the value an abstract parameter takes, and is substituted in when present.
          let concreteGuards := effectiveGuards p name ev
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
                   goal := goal, hyps := base ++
                     concreteGuards.filterMap fun q =>
                       (Formula.parse ((attrOf q "predicate").getD "")).toOption }]
          -- Simulation: whatever the abstract action does to a variable, the concrete
          -- event must do the same thing to it. The goal equates the two right-hand
          -- sides, with the concrete event's witnesses substituted into the abstract one.
          let concrete := actions.flatMap substOf
          for act in effectiveActions p am ae do
            let goal := match substOf act with
              | [(v, absRhs)] =>
                  match concrete.find? (fun q => q.1 == v) with
                  | some (_, conRhs) =>
                      some (Term.bin "=" conRhs (Formula.subst witnesses absRhs))
                  | none => none
              | _ => none
            out := out ++
              [{ name := labelOf ev ++ "/" ++ labelOf act ++ "/SIM", kind := "SIM",
                 goal := goal, hyps := base ++
                   ((effectiveGuards p name ev).filterMap fun q =>
                     (Formula.parse ((attrOf q "predicate").getD "")).toOption) }]
      for g in childrenOf ev "guard" do
        if wdRequired total ((attrOf g "predicate").getD "") then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf g ++ "/WD", kind := "WD",
               goal := wdGoal theory roots total types ((attrOf g "predicate").getD ""),
               hyps := eventHypsBefore p name ev g }]
      for act in childrenOf ev "action" do
        if wdRequired total ((attrOf act "assignment").getD "") then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf act ++ "/WD", kind := "WD",
               goal := wdGoal theory roots total types
                 ((attrOf act "assignment").getD ""),
               hyps := eventHyps p name ev }]
      for w in childrenOf ev "witness" do
        out := out ++
          [{ name := labelOf ev ++ "/" ++ labelOf w ++ "/WFIS", kind := "WFIS" }]
        if wdRequired total ((attrOf w "predicate").getD "") then
          out := out ++
            [{ name := labelOf ev ++ "/" ++ labelOf w ++ "/WWD", kind := "WWD" }]
    return finalize out

/-- Compatibility entry point for Rodin corpus projects without user theories. -/
def generate (p : Project) (name : String) : List Obligation :=
  generateIn Theory.empty p name

end EventB.POG
