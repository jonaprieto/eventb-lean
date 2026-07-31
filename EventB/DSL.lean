/-
Event-B written natively in Lean.

The elaborated form is the same `Elem` tree the `.bum` reader produces, so a model
authored here goes through the typechecker, the obligation generator and every gate
without any of them knowing where it came from. That is the whole design: one target
representation, two front ends.

Formulas are string literals parsed at elaboration time by `Formula.parse`, rather than
given Lean notation of their own. Event-B and Lean disagree about `∈`, `⊆`, `∪` and most
of the rest, so native notation would mean either shadowing Lean's or inventing a second
spelling of Event-B's; quoting sidesteps both and reuses the parser the corpus already
exercises. A formula that does not parse is an elaboration error pointing at the literal.

    eventb_context Ctx where
      sets AIRPLANES
      constants MAX
      axiom axm1 : "MAX ∈ ℕ"

    eventb_machine M sees Ctx where
      variables sched
      invariant inv1 : "sched ⊆ AIRPLANES"
      event Add where
        any a
        guard grd1 : "a ∈ AIRPLANES ∖ sched"
        action act1 : "sched ≔ sched ∪ {a}"

    #eventb_pog M
-/

import Lean
import EventB.POG

namespace EventB.DSL

open Lean Elab Command Term

declare_syntax_cat ebLabelled
syntax ident ":" str : ebLabelled
syntax "theorem " ident ":" str : ebLabelled

declare_syntax_cat ebEventPart
syntax "any " ident+ : ebEventPart
syntax "guard " ebLabelled : ebEventPart
syntax "action " ebLabelled : ebEventPart
syntax "witness " ebLabelled : ebEventPart
syntax "status " ident : ebEventPart

syntax "refines " ident : ebEventPart

declare_syntax_cat ebEvent
syntax "event " ident "where " ebEventPart* : ebEvent

declare_syntax_cat ebMachinePart
syntax "refines " ident : ebMachinePart
syntax "sees " ident+ : ebMachinePart
syntax "variables " ident+ : ebMachinePart
syntax "invariant " ebLabelled : ebMachinePart
syntax ebEvent : ebMachinePart

declare_syntax_cat ebContextPart
syntax "extends " ident+ : ebContextPart
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

private def eventAttrs (label : String) (conv : Option String) : TSyntax `term :=
  match conv with
  | none => Unhygienic.run `([("org.eventb.core.label", $(quote label))])
  | some s =>
      let convergence := if s == "convergent" then "1"
        else if s == "anticipated" then "2" else "0"
      Unhygienic.run `([("org.eventb.core.label", $(quote label)),
        ("org.eventb.core.convergence", $(quote convergence))])

private def noKids : TSyntax `term := Unhygienic.run `(([] : List EventB.Elem))

/-- Reject anything that is not an Event-B formula, at elaboration time. -/
private def checkFormula (stx : Syntax) (s : String) : CommandElabM Unit := do
  match Formula.parse s with
  | .ok _ => pure ()
  | .error e => throwErrorAt stx s!"not an Event-B formula: {e}"

private def labelledOf : TSyntax `ebLabelled → CommandElabM (String × String × Syntax × Bool)
  | `(ebLabelled| $l:ident : $f:str) => pure (l.getId.toString, f.getString, f, false)
  | `(ebLabelled| theorem $l:ident : $f:str) =>
      pure (l.getId.toString, f.getString, f, true)
  | stx => throwErrorAt stx "expected `label : \"formula\"`"

private def mkElem (ctor : String) (attrs kids : TSyntax `term) : TSyntax `term :=
  Unhygienic.run `($(mkIdent ("EventB.Elem." ++ ctor : String).toName) $attrs $kids)

private def listOf (ts : Array (TSyntax `term)) : TSyntax `term :=
  Unhygienic.run `([$ts,*])

private def eventParts (parts : Array (TSyntax `ebEventPart)) :
    CommandElabM (Array (TSyntax `term) × Option String) := do
  let mut out := #[]
  let mut conv : Option String := none
  for p in parts do
    match p with
    | `(ebEventPart| refines $r:ident) =>
        out := out.push (mkElem "refinesEvent" (targetAttrs r.getId.toString) noKids)
    | `(ebEventPart| any $xs:ident*) =>
        for x in xs do
          out := out.push (mkElem "parameter" (identAttrs x.getId.toString) noKids)
    | `(ebEventPart| guard $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula stx f
        out := out.push (mkElem "guard"
          (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
    | `(ebEventPart| action $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula stx f
        out := out.push (mkElem "action"
          (labelledAttrs "org.eventb.core.assignment" lab f isThm) noKids)
    | `(ebEventPart| witness $l:ebLabelled) =>
        let (lab, f, stx, isThm) ← labelledOf l
        checkFormula stx f
        out := out.push (mkElem "witness"
          (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
    | `(ebEventPart| status $s:ident) => conv := some s.getId.toString
    | stx => throwErrorAt stx "unexpected event clause"
  return (out, conv)

private def eventOf (stx : TSyntax `ebEvent) : CommandElabM (TSyntax `term) := do
  match stx with
  | `(ebEvent| event $n:ident where $ps:ebEventPart*) => do
      let (kids, conv) ← eventParts ps
      let attrs := eventAttrs n.getId.toString conv
      return mkElem "event" attrs (listOf kids)
  | other => throwErrorAt other "expected an event"

syntax (name := eventbMachine)
  "eventb_machine " ident "where " ebMachinePart* : command

syntax (name := eventbContext)
  "eventb_context " ident "where " ebContextPart* : command

/-- Emit `def <name> : EventB.Elem := <tree>`, so the model is an ordinary Lean value
that the generator and the typechecker consume unchanged. -/
private def define (name : Ident) (body : TSyntax `term) : CommandElabM Unit := do
  elabCommand (← `(def $name : EventB.Elem := $body))

@[command_elab eventbMachine]
private def elabMachine : CommandElab := fun stx => do
  match stx with
  | `(eventb_machine $n:ident where $ps:ebMachinePart*) => do
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
        | `(ebMachinePart| variables $xs:ident*) =>
            for x in xs do
              kids := kids.push
                (mkElem "variable" (identAttrs x.getId.toString) noKids)
        | `(ebMachinePart| invariant $l:ebLabelled) =>
            let (lab, f, s, isThm) ← labelledOf l
            checkFormula s f
            kids := kids.push (mkElem "invariant"
              (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
        | `(ebMachinePart| $e:ebEvent) => kids := kids.push (← eventOf e)
        | other => throwErrorAt other "unexpected machine clause"
      define n (mkElem "machineFile" (Unhygienic.run `(([] : List (String × String))))
        (listOf kids))
  | _ => throwUnsupportedSyntax

@[command_elab eventbContext]
private def elabContext : CommandElab := fun stx => do
  match stx with
  | `(eventb_context $n:ident where $ps:ebContextPart*) => do
      let mut kids : Array (TSyntax `term) := #[]
      for p in ps do
        match p with
        | `(ebContextPart| extends $es:ident*) =>
            for e in es do
              kids := kids.push
                (mkElem "extendsContext" (targetAttrs e.getId.toString) noKids)
        | `(ebContextPart| sets $xs:ident*) =>
            for x in xs do
              kids := kids.push
                (mkElem "carrierSet" (identAttrs x.getId.toString) noKids)
        | `(ebContextPart| constants $xs:ident*) =>
            for x in xs do
              kids := kids.push (mkElem "constant" (identAttrs x.getId.toString) noKids)
        | `(ebContextPart| axiom $l:ebLabelled) =>
            let (lab, f, s, isThm) ← labelledOf l
            checkFormula s f
            kids := kids.push (mkElem "axiom"
              (labelledAttrs "org.eventb.core.predicate" lab f isThm) noKids)
        | other => throwErrorAt other "unexpected context clause"
      define n (mkElem "contextFile" (Unhygienic.run `(([] : List (String × String))))
        (listOf kids))
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
