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

private def elementWith (tag : String) (attributes : List (String × Json))
    (children : List Html) : Html :=
  .element tag attributes.toArray children.toArray

private def element (tag : String) (children : List Html) : Html :=
  elementWith tag [] children

private def text (value : String) : Html := .text value

private def classes (value : String) : String × Json := ("className", .str value)

private def badge (label colorClass : String) : Html :=
  elementWith "span" [classes s!"f7 b dib ml2 ph1 ba br-pill {colorClass}"] [text label]

private def formula (value : Formula.Term) : Html :=
  elementWith "pre" [classes "overflow-auto mv2 pa2 ba br1"] [
      element "code" [text (Formula.print value)]
    ]

private def hypothesisList (hyps : List Formula.Term) : Html :=
  if hyps.isEmpty then
    elementWith "p" [classes "mv1 o-70"] [text "none"]
  else
    elementWith "ul" [classes "mv2 pl3"]
      (hyps.map fun hypothesis => element "li" [formula hypothesis])

private def obligationBody (obligation : Obligation) : Html :=
  elementWith "div" [classes "pa2"] [
    elementWith "p" [classes "mv1 o-70"] [
      text s!"{obligation.hyps.length} hypotheses"
    ],
    elementWith "h4" [classes "mt2 mb1 f6"] [
      text "Hypotheses"
    ],
    hypothesisList obligation.hyps,
    elementWith "h4" [classes "mt2 mb1 f6"] [text "Goal"],
    match obligation.goal with
    | some goal => elementWith "div" [classes "bl bw2 b--blue pl2"] [
        formula goal
      ]
    | none => elementWith "p" [classes "mv1 o-70"] [
        text "No statement derived yet."
      ]
  ]

private def kindClass : String → String
  | "INV" => "blue"
  | "GRD" => "gold"
  | "SIM" => "purple"
  | "WD" => "teal"
  | "THM" => "green"
  | "WFIS" => "light-blue"
  | "WWD" => "red"
  | _ => "grey"

private def kindTitle : String → String
  | "INV" => "Invariant preservation"
  | "GRD" => "Guard strengthening"
  | "SIM" => "Action simulation"
  | "WD" => "Well-definedness"
  | "THM" => "Theorem"
  | "WFIS" => "Witness feasibility"
  | "WWD" => "Witness well-definedness"
  | kind => kind

private def obligationCard (obligation : Obligation) : Html :=
  elementWith "details" [classes "mv1 ba br1"] [
    elementWith "summary" [classes "pointer pa2"] [
      text obligation.name,
      badge (if obligation.goal.isSome then "derived" else "pending")
        (if obligation.goal.isSome then "green" else "red")
    ],
    obligationBody obligation
  ]

private def kinds : List String := ["INV", "WD", "GRD", "SIM", "THM", "WFIS", "WWD"]

private def countKind (kind : String) (obligations : List Obligation) : Nat :=
  obligations.countP (·.kind == kind)

private def countDerived (obligations : List Obligation) : Nat :=
  obligations.countP (·.goal.isSome)

private def stat (label value accent : String) : Html :=
  elementWith "div" [classes "ba br2 pa2 mr2 mb2"] [
      elementWith "div" [classes s!"f3 b {accent}"] [text value],
      elementWith "div" [classes "f7 o-70"] [text label]
    ]

private def summary (obligations : List Obligation) : Html :=
  elementWith "div" [classes "flex flex-wrap mv2"] [
      stat "total obligations" (toString obligations.length) "blue",
      stat "goals derived" (toString (countDerived obligations)) "green",
      stat "obligation classes"
        (toString (kinds.countP (fun kind => countKind kind obligations > 0))) "purple"
    ]

private def openAttribute (isOpen : Bool) : List (String × Json) :=
  if isOpen then [("open", .bool true)] else []

private def kindSection (kind : String) (obligations : List Obligation) (isOpen : Bool) :
    Option Html :=
  if obligations.isEmpty then
    none
  else
    some <| elementWith "details"
      (openAttribute isOpen ++ [classes "mv2 ba br2"]) [
      elementWith "summary" [classes "pointer pa2 b"] [
        badge kind (kindClass kind),
        text s!"{kindTitle kind} · {obligations.length}"
      ],
      elementWith "div" [classes "pa1"]
        (obligations.map obligationCard)
    ]

private def firstKind (obligations : List Obligation) : Option String :=
  kinds.find? (fun kind => countKind kind obligations > 0)

/-- Render the obligations for a project component in the Lean Infoview. -/
def renderProject (project : Typing.Project) (machine : String) : Html :=
  let obligations := POG.generate project machine
  let first := firstKind obligations
  let sections := kinds.filterMap fun kind =>
    kindSection kind (obligations.filter (·.kind == kind)) (first == some kind)
  elementWith "section" [classes "pa2"] [
    elementWith "header" [classes "mb2"] [
      elementWith "h3" [classes "f3 b mv1"] [
        text s!"Event-B obligations · {machine}"
      ],
      elementWith "p" [classes "mv1 o-70"] [
        text "Proof-obligation explorer · expand a class, then an obligation"
      ]
    ],
    summary obligations,
    if sections.isEmpty then element "p" [text "No obligations generated."]
    else element "div" sections
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
