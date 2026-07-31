/-
Proof-obligation display for the Lean Infoview.

This is a separate library so the parser, POG, CLI and corpus gates do not depend on
the editor UI. The widget only renders data already produced by `EventB.POG.generate`.
-/

import EventB.DSL
import ProofWidgets.Component.HtmlDisplay

namespace EventB.Widgets

open Lean Server Elab Command
open EventB Formula POG ProofWidgets

private def element (tag : String) (children : List Html) : Html :=
  .element tag #[] children.toArray

private def text (value : String) : Html := .text value

private def formula (value : Formula.Term) : Html :=
  element "pre" [element "code" [text (Formula.print value)]]

private def hypothesisList (hyps : List Formula.Term) : Html :=
  if hyps.isEmpty then
    element "p" [text "none"]
  else
    element "ul" (hyps.map fun hypothesis =>
      element "li" [formula hypothesis])

private def obligationBody (obligation : Obligation) : Html :=
  element "div" [
    element "p" [text s!"kind: {obligation.kind}"],
    element "h4" [text "Hypotheses"],
    hypothesisList obligation.hyps,
    element "h4" [text "Goal"],
    match obligation.goal with
    | some goal => formula goal
    | none => element "p" [text "no statement derived"]
  ]

private def obligationCard (obligation : Obligation) : Html :=
  element "details" [
    element "summary" [text s!"{obligation.name} [{obligation.kind}]"],
    obligationBody obligation
  ]

private def kinds : List String := ["INV", "WD", "GRD", "SIM", "THM", "WFIS", "WWD"]

private def countKind (kind : String) (obligations : List Obligation) : Nat :=
  obligations.countP (·.kind == kind)

private def summary (obligations : List Obligation) : Html :=
  let counts := kinds.filterMap fun kind =>
    let count := countKind kind obligations
    if count == 0 then none else some s!"{kind} {count}"
  element "p" [text s!"{obligations.length} obligations: {String.intercalate ", " counts}"]

/-- Render the obligations for a project component in the Lean Infoview. -/
def renderProject (project : Typing.Project) (machine : String) : Html :=
  let obligations := POG.generate project machine
  element "section" [
    element "h3" [text s!"Event-B obligations: {machine}"],
    summary obligations,
    if obligations.isEmpty then
      element "p" [text "No obligations generated."]
    else
      element "div" (obligations.map obligationCard)
  ]

/-- Display generated obligations without changing the ordinary text POG command. -/
syntax (name := eventbPogWidget) "#eventb_pog_widget " ident ident : command

@[command_elab eventbPogWidget]
private def elabPogWidget : CommandElab := fun stx => do
  match stx with
  | `(#eventb_pog_widget $project:ident $machine:ident) => do
      let render ← `(EventB.Widgets.renderProject $project
        $(quote machine.getId.toString))
      let htmlX ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml
        <| ← ``(ProofWidgets.HtmlEval.eval $render)
      let html ← htmlX
      liftCoreM <| Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return json% { html: $(← rpcEncode html) })
        stx
  | _ => throwUnsupportedSyntax

end EventB.Widgets
