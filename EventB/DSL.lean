/-
Event-B written natively in Lean.

The elaborated form is the same `Elem` tree the `.bum` reader produces, so a model
authored here goes through the typechecker, the obligation generator and every gate
without any of them knowing where it came from. That is the whole design: one target
representation, two front ends.

Formulas are parsed at elaboration time by `Formula.parse`. The DSL accepts ordinary Lean
term syntax for predicates, while quoted formulas remain available for Event-B operators
that Lean does not parse. Actions may use Lean's `:=` spelling for Event-B's `≔`.

Formula identifiers are scope-checked against the component closure, and unquoted
references carry native Lean server locations for Go to Definition.

    eventb_context Ctx where
      sets AIRPLANES
      constants MAX
      axiom axm1 : MAX ∈ ℕ

    eventb_machine M sees Ctx where
      variables sched
      invariant inv1 : sched ⊆ AIRPLANES
      event Add where
        any a
        guard grd1 : "a ∈ AIRPLANES ∖ sched"
        action act1 : sched := sched ∪ {a}

    #eventb_pog M
-/

import Lean
import EventB.POG

namespace EventB.DSL

open Lean Elab Command Term
open EventB.Prelude EventB.Typing

initialize theoryExtension : SimplePersistentEnvExtension Theory.Spec (Array Theory.Spec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id
  }

private def theoryEnvironment (env : Environment) : Theory.Env :=
  { theories := Theory.core :: (theoryExtension.getState env).toList }

declare_syntax_cat ebLabelled
declare_syntax_cat ebFormula
syntax str : ebFormula
syntax:12 term "⇒" term : ebFormula
syntax:12 term "=>" term : ebFormula
syntax:50 term ":=" term : ebFormula
syntax term : ebFormula
syntax ident ":" ebFormula : ebLabelled
syntax "theorem " ident ":" ebFormula : ebLabelled

declare_syntax_cat ebEventPart
syntax "any " ident+ : ebEventPart
syntax "guard " ebLabelled : ebEventPart
syntax "action " ebLabelled : ebEventPart
syntax "witness " ebLabelled : ebEventPart
syntax "status " ident : ebEventPart

syntax "refines " ident : ebEventPart
syntax "extends " ident : ebEventPart

declare_syntax_cat ebEvent
syntax "event " ident "where " ebEventPart* : ebEvent

declare_syntax_cat ebMachinePart
syntax "refines " ident : ebMachinePart
syntax "sees " ident+ : ebMachinePart
syntax "theories " ident+ : ebMachinePart
syntax "variables " ident+ : ebMachinePart
syntax "invariant " ebLabelled : ebMachinePart
syntax "variant " ebLabelled : ebMachinePart
syntax ebEvent : ebMachinePart

declare_syntax_cat ebContextPart
syntax "extends " ident+ : ebContextPart
syntax "theories " ident+ : ebContextPart
syntax "sets " ident+ : ebContextPart
syntax "constants " ident+ : ebContextPart
syntax "axiom " ebLabelled : ebContextPart

/-- Attribute list for a labelled child: `@[label] formula`. -/
private def labelledAttrs (attr label formula : String) (isThm : Bool) : TSyntax `term :=
  if isThm then
    Unhygienic.run `([("org.eventb.core.label", $(quote label)),
      ($(quote attr), $(quote formula)), ("org.eventb.core.theorem", "true")])
  else
    Unhygienic.run
      `([("org.eventb.core.label", $(quote label)), ($(quote attr), $(quote formula))])

private def identAttrs (name : String) : TSyntax `term :=
  Unhygienic.run `([("org.eventb.core.identifier", $(quote name))])

private def targetAttrs (name : String) : TSyntax `term :=
  Unhygienic.run `([("org.eventb.core.target", $(quote name))])

private def extendedTargetAttrs (name : String) : TSyntax `term :=
  Unhygienic.run `([("org.eventb.core.target", $(quote name)),
    ("org.eventb.core.extended", "true")])

private def eventAttrs (label : String) (conv : Option String) : TSyntax `term :=
  match conv with
  | none => Unhygienic.run `([("org.eventb.core.label", $(quote label))])
  | some s =>
      let convergence := if s == "convergent" then "1"
        else if s == "anticipated" then "2" else "0"
      Unhygienic.run `([("org.eventb.core.label", $(quote label)),
        ("org.eventb.core.convergence", $(quote convergence))])

private def noKids : TSyntax `term := Unhygienic.run `(([] : List EventB.Elem))

private def symbolName (owner symbol : String) : Name :=
  Name.mkSimple ("EventB.DSL.symbol." ++ owner ++ "." ++ symbol)

private def addSymbolRange (owner : String) (id : Syntax) : CommandElabM Unit := do
  let some range ← getDeclarationRange? id | return
  Lean.addDeclarationRanges (symbolName owner id.getId.toString)
    { range := range, selectionRange := range }

private def baseSymbol (symbol : String) : String :=
  if symbol.endsWith "'" then (symbol.dropEnd 1).copy else symbol

private def currentModule : CommandElabM Name := do
  let fileName ← getFileName
  try
    let path ← liftIO <| IO.FS.realPath (System.FilePath.mk fileName)
    pure <| Name.str .anonymous ("external:" ++ System.Uri.pathToUri path)
  catch _ =>
    getMainModule

private def symbolLocation? (owners : List String) (symbol : String) :
    CommandElabM (Option DeclarationLocation) := do
  let module ← currentModule
  let symbol := baseSymbol symbol
  for owner in owners do
    if let some ranges ← Lean.findDeclarationRanges? (symbolName owner symbol) then
      return some { module, range := ranges.selectionRange }
  return none

private def formulaIdentifiersAux : Nat → Syntax → List Syntax
  | 0, _ => []
  | fuel + 1, stx =>
    if stx.isIdent then [stx]
    else stx.getArgs.toList.flatMap (formulaIdentifiersAux fuel)

private def formulaIdentifiers (stx : Syntax) : List Syntax :=
  -- Formula syntax is shallow; the bound keeps this metadata walk executable.
  formulaIdentifiersAux 1024 stx

private def freeFormulaIdentifiers (bound : List String) : Formula.Term → List String
  | .id n => if bound.contains n then [] else [n]
  | .num _ => []
  | .bin _ a b => freeFormulaIdentifiers bound a ++ freeFormulaIdentifiers bound b
  | .pre _ a | .post _ a => freeFormulaIdentifiers bound a
  | .app f a | .img f a => freeFormulaIdentifiers bound f ++ freeFormulaIdentifiers bound a
  | .set ts => ts.flatMap (freeFormulaIdentifiers bound)
  | .bind _ pattern body =>
      let bound' := Formula.patternNames pattern ++ bound
      freeFormulaIdentifiers bound' pattern ++ freeFormulaIdentifiers bound' body

private def checkScope (theoryRoots owners : List String) (stx : Syntax) (term : Formula.Term) :
    CommandElabM Unit := do
  let theory := theoryEnvironment (← getEnv)
  for name in (freeFormulaIdentifiers [] term).eraseDups do
    if !Theory.isIdentifierIn theory theoryRoots name && (← symbolLocation? owners name).isNone then
      throwErrorAt stx s!"unknown Event-B identifier `{name}`"

private def addDefinitionInfo (id : Syntax) (symbol : String) (location : DeclarationLocation) :
    CommandElabM Unit := do
  pushInfoLeaf <| .ofDelabTermInfo {
    elaborator := `EventB.DSL
    stx := id
    lctx := {}
    expectedType? := none
    expr := mkStrLit symbol
    location? := some location
    docString? := some s!"Event-B symbol `{symbol}`"
  }

private def addFormulaInfos (owners : List String) (stx : Syntax) : CommandElabM Unit := do
  for id in formulaIdentifiers stx do
    if let some location ← symbolLocation? owners id.getId.toString then
      addDefinitionInfo id id.getId.toString location

/-- Reject anything that is not an Event-B formula, at elaboration time. -/
private def checkFormula (theoryRoots owners : List String) (stx : Syntax) (s : String) :
    CommandElabM Unit := do
  match Formula.parse s with
  | .ok term => checkScope theoryRoots owners stx term
  | .error e => throwErrorAt stx s!"not an Event-B formula: {e}"

private def formulaText (f : TSyntax `ebFormula) : String :=
  match f with
  | `(ebFormula| $s:str) => s.getString
  | _ => f.raw.prettyPrint.pretty

private def labelledOf : TSyntax `ebLabelled → CommandElabM (String × String × Syntax × Bool)
  | `(ebLabelled| $l:ident : $f:ebFormula) =>
      pure (l.getId.toString, formulaText f, f.raw, false)
  | `(ebLabelled| theorem $l:ident : $f:ebFormula) =>
      pure (l.getId.toString, formulaText f, f.raw, true)
  | stx => throwErrorAt stx "expected `label : formula`"

private def mkElem (ctor : String) (attrs kids : TSyntax `term) : TSyntax `term :=
  Unhygienic.run `($(mkIdent ("EventB.Elem." ++ ctor : String).toName) $attrs $kids)

private def listOf (ts : Array (TSyntax `term)) : TSyntax `term :=
  Unhygienic.run `([$ts,*])

private def eventParts (theoryRoots owners : List String) (parts : Array (TSyntax `ebEventPart)) :
    CommandElabM (Array (TSyntax `term) × Option String) := do
  let mut out := #[]
  let mut conv : Option String := none
  for p in parts do
    match p with
    | `(ebEventPart| refines $r:ident) =>
        out := out.push (mkElem "refinesEvent" (targetAttrs r.getId.toString) noKids)
    | `(ebEventPart| extends $r:ident) =>
        out := out.push
          (mkElem "refinesEvent" (extendedTargetAttrs r.getId.toString) noKids)
    | `(ebEventPart| any $xs:ident*) =>
        for x in xs do
          out := out.push (mkElem "parameter" (identAttrs x.getId.toString) noKids)
    | `(ebEventPart| guard $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula theoryRoots owners stx f
        out := out.push (mkElem "guard"
          (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
    | `(ebEventPart| action $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula theoryRoots owners stx f
        out := out.push (mkElem "action"
          (labelledAttrs "org.eventb.core.assignment" lab f isThm) noKids)
    | `(ebEventPart| witness $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula theoryRoots owners stx f
        out := out.push (mkElem "witness"
          (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
    | `(ebEventPart| status $s:ident) => conv := some s.getId.toString
    | stx => throwErrorAt stx "unexpected event clause"
  return (out, conv)

private def eventOf (owner : String) (theoryRoots owners : List String) (stx : TSyntax `ebEvent) :
    CommandElabM (TSyntax `term) := do
  match stx with
  | `(ebEvent| event $n:ident where $ps:ebEventPart*) => do
      let eventOwner := owner ++ "." ++ n.getId.toString
      for p in ps do
        match p with
        | `(ebEventPart| any $xs:ident*) =>
            for x in xs do addSymbolRange eventOwner x.raw
        | _ => pure ()
      let (kids, conv) ← eventParts theoryRoots (eventOwner :: owners) ps
      let attrs := eventAttrs n.getId.toString conv
      return mkElem "event" attrs (listOf kids)
  | other => throwErrorAt other "expected an event"

private def addEventInfos (owner : String) (owners : List String)
    (stx : TSyntax `ebEvent) : CommandElabM Unit := do
  match stx with
  | `(ebEvent| event $n:ident where $ps:ebEventPart*) =>
      let eventOwner := owner ++ "." ++ n.getId.toString
      for p in ps do
        match p with
        | `(ebEventPart| guard $l:ebLabelled) =>
            let (_, _, s, _) ← labelledOf l
            addFormulaInfos (eventOwner :: owners) s
        | `(ebEventPart| action $l:ebLabelled) =>
            let (_, _, s, _) ← labelledOf l
            addFormulaInfos (eventOwner :: owners) s
        | `(ebEventPart| witness $l:ebLabelled) =>
            let (_, _, s, _) ← labelledOf l
            addFormulaInfos (eventOwner :: owners) s
        | _ => pure ()
  | other => throwErrorAt other "expected an event"

private def addMachineInfos (owner : String) (owners : List String)
    (parts : Array (TSyntax `ebMachinePart)) : CommandElabM Unit := do
  for p in parts do
    match p with
    | `(ebMachinePart| invariant $l:ebLabelled) =>
        let (_, _, s, _) ← labelledOf l
        addFormulaInfos owners s
    | `(ebMachinePart| variant $l:ebLabelled) =>
        let (_, _, s, _) ← labelledOf l
        addFormulaInfos owners s
    | `(ebMachinePart| $e:ebEvent) => addEventInfos owner owners e
    | _ => pure ()

private def addContextInfos (owners : List String)
    (parts : Array (TSyntax `ebContextPart)) : CommandElabM Unit := do
  for p in parts do
    match p with
    | `(ebContextPart| axiom $l:ebLabelled) =>
        let (_, _, s, _) ← labelledOf l
        addFormulaInfos owners s
    | _ => pure ()

syntax (name := eventbMachine)
  "eventb_machine " ident "where " ebMachinePart* : command

syntax (name := eventbContext)
  "eventb_context " ident "where " ebContextPart* : command

declare_syntax_cat ebTheoryPart
syntax "imports " ident+ : ebTheoryPart
syntax "carrier " ident+ : ebTheoryPart
syntax "constant " ident ":" ident : ebTheoryPart
syntax "predicate " ident : ebTheoryPart
syntax "expression " ident : ebTheoryPart
syntax "well_defined " ident : ebTheoryPart

syntax (name := eventbTheory)
  "eventb_theory " ident "where " ebTheoryPart* : command

private def theoryTy (stx : Syntax) : EventB.Typing.Ty :=
  (EventB.Typing.Ty.parse stx.getId.toString).getD (.given stx.getId.toString)

private def mkTyTerm : EventB.Typing.Ty → TSyntax `term
  | .int => Unhygienic.run `(EventB.Typing.Ty.int)
  | .bool => Unhygienic.run `(EventB.Typing.Ty.bool)
  | .given name => Unhygienic.run `(EventB.Typing.Ty.given $(quote name))
  | .mvar index => Unhygienic.run `(EventB.Typing.Ty.mvar $(quote index))
  | .pow inner => Unhygienic.run `(EventB.Typing.Ty.pow $(mkTyTerm inner))
  | .prod left right =>
      Unhygienic.run `(EventB.Typing.Ty.prod $(mkTyTerm left) $(mkTyTerm right))

private def mkSymbolKind (kind : SymbolKind) : TSyntax `term :=
  match kind with
  | .carrierSet => Unhygienic.run `(EventB.Prelude.SymbolKind.carrierSet)
  | .constant => Unhygienic.run `(EventB.Prelude.SymbolKind.constant)
  | .predicate => Unhygienic.run `(EventB.Prelude.SymbolKind.predicate)
  | .expression => Unhygienic.run `(EventB.Prelude.SymbolKind.expression)

private def mkApplication (application : Option ApplicationKind) : TSyntax `term :=
  match application with
  | none => Unhygienic.run `(none)
  | some .total => Unhygienic.run `(some EventB.Prelude.ApplicationKind.total)
  | some .wellDefined => Unhygienic.run `(some EventB.Prelude.ApplicationKind.wellDefined)

private def mkSymbolTerm (symbol : Symbol) : TSyntax `term :=
  let type := match symbol.type with
    | none => Unhygienic.run `(none)
    | some type => Unhygienic.run `(some $(mkTyTerm type))
  Unhygienic.run `(EventB.Prelude.Symbol.mk $(quote symbol.name) $(mkSymbolKind symbol.kind)
    $type $(quote symbol.description) $(mkApplication symbol.application))

private def mkSpecTerm (spec : Theory.Spec) : TSyntax `term :=
  let importNames := listOf (spec.imports.toArray.map quote)
  let symbols := listOf (spec.symbols.toArray.map mkSymbolTerm)
  Unhygienic.run `(EventB.Theory.Spec.mk $(quote spec.name) $importNames $symbols)

private def theorySymbol (name : String) (kind : SymbolKind) (type : Option Ty)
    (application : Option ApplicationKind) : Symbol :=
  { name, kind, type, description := s!"Native Event-B theory symbol `{name}`.", application }

private def defineTheory (name : Ident) (body : TSyntax `term) : CommandElabM Unit := do
  elabCommand (← `(def $name : EventB.Theory.Spec := $body))

@[command_elab eventbTheory]
private def elabTheory : CommandElab := fun stx => do
  match stx with
  | `(eventb_theory $n:ident where $ps:ebTheoryPart*) => do
      let mut importNames : List String := []
      let mut symbols : List Symbol := []
      for p in ps do
        match p with
        | `(ebTheoryPart| imports $xs:ident*) =>
            importNames := importNames ++ xs.toList.map (·.getId.toString)
        | `(ebTheoryPart| carrier $xs:ident*) =>
            for x in xs do
              let name := x.getId.toString
              symbols := symbols ++
                [theorySymbol name .carrierSet (some (.pow (.given name))) none]
        | `(ebTheoryPart| constant $x:ident : $t:ident) =>
            symbols := symbols ++
              [theorySymbol x.getId.toString .constant (some (theoryTy t)) none]
        | `(ebTheoryPart| predicate $x:ident) =>
            symbols := symbols ++
              [theorySymbol x.getId.toString .predicate none (some .total)]
        | `(ebTheoryPart| expression $x:ident) =>
            symbols := symbols ++
              [theorySymbol x.getId.toString .expression none (some .total)]
        | `(ebTheoryPart| well_defined $x:ident) =>
            symbols := symbols ++
              [theorySymbol x.getId.toString .expression none (some .wellDefined)]
        | other => throwErrorAt other "unexpected theory clause"
      let spec : Theory.Spec :=
        Theory.Spec.mk n.getId.toString importNames symbols
      match Theory.add (theoryEnvironment (← getEnv)) spec with
      | .error message => throwErrorAt n message
      | .ok _ =>
          defineTheory n (mkSpecTerm spec)
          modifyEnv (theoryExtension.addEntry · spec)
  | _ => throwUnsupportedSyntax

/-- Emit `def <name> : EventB.Elem := <tree>`, so the model is an ordinary Lean value
that the generator and the typechecker consume unchanged. -/
private def define (name : Ident) (body : TSyntax `term) : CommandElabM Unit := do
  elabCommand (← `(def $name : EventB.Elem := $body))

@[command_elab eventbMachine]
private def elabMachine : CommandElab := fun stx => do
  match stx with
  | `(eventb_machine $n:ident where $ps:ebMachinePart*) => do
      let owner := n.getId.toString
      let mut owners := [owner]
      let mut theoryRoots : List String := []
      for p in ps do
        match p with
        | `(ebMachinePart| refines $r:ident) => owners := owners ++ [r.getId.toString]
        | `(ebMachinePart| sees $ss:ident*) =>
            for s in ss do owners := owners ++ [s.getId.toString]
        | `(ebMachinePart| theories $ts:ident*) =>
            theoryRoots := theoryRoots ++ ts.toList.map (·.getId.toString)
        | _ => pure ()
      for p in ps do
        match p with
        | `(ebMachinePart| variables $xs:ident*) =>
            for x in xs do addSymbolRange owner x.raw
        | _ => pure ()
      let mut kids : Array (TSyntax `term) := #[]
      for p in ps do
        match p with
        | `(ebMachinePart| refines $r:ident) =>
            kids := kids.push
              (mkElem "refinesMachine" (targetAttrs r.getId.toString) noKids)
        | `(ebMachinePart| sees $ss:ident*) =>
            for sc in ss do
              kids := kids.push
                (mkElem "seesContext" (targetAttrs sc.getId.toString) noKids)
        | `(ebMachinePart| theories $_:ident*) => pure ()
        | `(ebMachinePart| variables $xs:ident*) =>
            for x in xs do
              kids := kids.push
                (mkElem "variable" (identAttrs x.getId.toString) noKids)
        | `(ebMachinePart| invariant $l:ebLabelled) =>
            let (lab, f, s, isThm) ← labelledOf l
            checkFormula theoryRoots owners s f
            kids := kids.push (mkElem "invariant"
              (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
        | `(ebMachinePart| variant $l:ebLabelled) =>
            let (lab, f, s, isThm) ← labelledOf l
            checkFormula theoryRoots owners s f
            kids := kids.push (mkElem "variant"
              (labelledAttrs "org.eventb.core.expression" lab f isThm) noKids)
        | `(ebMachinePart| $e:ebEvent) =>
            kids := kids.push (← eventOf owner theoryRoots owners e)
        | other => throwErrorAt other "unexpected machine clause"
      define n (mkElem "machineFile" (Unhygienic.run `(([] : List (String × String))))
        (listOf kids))
      addMachineInfos owner owners ps
  | _ => throwUnsupportedSyntax

@[command_elab eventbContext]
private def elabContext : CommandElab := fun stx => do
  match stx with
  | `(eventb_context $n:ident where $ps:ebContextPart*) => do
      let owner := n.getId.toString
      let mut owners := [owner]
      let mut theoryRoots : List String := []
      for p in ps do
        match p with
        | `(ebContextPart| extends $es:ident*) =>
            for e in es do owners := owners ++ [e.getId.toString]
        | `(ebContextPart| theories $ts:ident*) =>
            theoryRoots := theoryRoots ++ ts.toList.map (·.getId.toString)
        | _ => pure ()
      for p in ps do
        match p with
        | `(ebContextPart| sets $xs:ident*) =>
            for x in xs do addSymbolRange owner x.raw
        | `(ebContextPart| constants $xs:ident*) =>
            for x in xs do addSymbolRange owner x.raw
        | _ => pure ()
      let mut kids : Array (TSyntax `term) := #[]
      for p in ps do
        match p with
        | `(ebContextPart| extends $es:ident*) =>
            for e in es do
              kids := kids.push
                (mkElem "extendsContext" (targetAttrs e.getId.toString) noKids)
        | `(ebContextPart| theories $_:ident*) => pure ()
        | `(ebContextPart| sets $xs:ident*) =>
            for x in xs do
              kids := kids.push
                (mkElem "carrierSet" (identAttrs x.getId.toString) noKids)
        | `(ebContextPart| constants $xs:ident*) =>
            for x in xs do
              kids := kids.push (mkElem "constant" (identAttrs x.getId.toString) noKids)
        | `(ebContextPart| axiom $l:ebLabelled) =>
            let (lab, f, s, isThm) ← labelledOf l
            checkFormula theoryRoots owners s f
            kids := kids.push (mkElem "axiom"
              (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
        | other => throwErrorAt other "unexpected context clause"
      define n (mkElem "contextFile" (Unhygienic.run `(([] : List (String × String))))
        (listOf kids))
      addContextInfos owners ps
  | _ => throwUnsupportedSyntax

/-- `#eventb_pog M Ctx ...` prints the obligations generated for the first named
component, resolving the rest as its project. The point of the DSL is that this is the
same generator the corpus goes through, so what it prints here is what a `.bum` would
get. -/
syntax (name := eventbPog) "#eventb_pog " ident+ : command

@[command_elab eventbPog]
private def elabPog : CommandElab := fun stx => do
  match stx with
  | `(#eventb_pog $ns:ident*) => do
      let head := ns[0]!.getId.toString
      let entries : Array (TSyntax `term) ← ns.mapM fun n => do
        `(({ name := $(quote n.getId.toString), elem := $(mkIdent n.getId) } :
            EventB.Typing.Component))
      elabCommand (← `(#eval show IO Unit from do
        let project : EventB.Typing.Project := [$entries,*]
        for o in EventB.POG.generate project $(quote head) do
          IO.println s!"{o.name}"
          match o.goal with
          | some g => IO.println s!"    ⊢ {EventB.Formula.print g}"
          | none => pure ()))
  | _ => throwUnsupportedSyntax

end EventB.DSL
