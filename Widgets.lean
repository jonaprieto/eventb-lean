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

private def style (value : String) : String × Json := ("style", .str value)

private def badge (label color : String) : Html :=
  elementWith "span" [style (s!"color:{color};font-size:.75em;font-weight:700;" ++
    "letter-spacing:.03em;margin-left:.5rem;padding:.15rem .4rem;" ++
    "border:1px solid {color};border-radius:999px;")] [text label]

private def formula (value : Formula.Term) : Html :=
  elementWith "pre" [style ("overflow-x:auto;margin:.35rem 0;padding:.5rem;" ++
    "border-radius:4px;background:rgba(127,127,127,.12);")] [
      element "code" [text (Formula.print value)]
    ]

private def hypothesisList (hyps : List Formula.Term) : Html :=
  if hyps.isEmpty then
    elementWith "p" [style "opacity:.7;margin:.25rem 0;"] [text "none"]
  else
    elementWith "ul" [style "margin:.25rem 0;padding-left:1.25rem;"]
      (hyps.map fun hypothesis => element "li" [formula hypothesis])

private def obligationBody (obligation : Obligation) : Html :=
  elementWith "div" [style "padding:.25rem .75rem .75rem;"] [
    elementWith "p" [style "margin:.35rem 0;opacity:.75;"] [
      text s!"{obligation.hyps.length} hypotheses"
    ],
    elementWith "h4" [style "margin:.6rem 0 .2rem;font-size:.85em;"] [
      text "Hypotheses"
    ],
    hypothesisList obligation.hyps,
    elementWith "h4" [style "margin:.6rem 0 .2rem;font-size:.85em;"] [text "Goal"],
    match obligation.goal with
    | some goal => elementWith "div" [style "border-left:3px solid #4da3ff;"] [
        formula goal
      ]
    | none => elementWith "p" [style "opacity:.7;margin:.25rem 0;"] [
        text "No statement derived yet."
      ]
  ]

private def kindColor : String → String
  | "INV" => "#4da3ff"
  | "GRD" => "#e5c07b"
  | "SIM" => "#c678dd"
  | "WD" => "#56b6c2"
  | "THM" => "#98c379"
  | "WFIS" => "#61afef"
  | "WWD" => "#e06c75"
  | _ => "#abb2bf"

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
  elementWith "details" [style ("margin:.35rem 0;border:1px solid rgba(127,127,127,.3);" ++
    "border-left:3px solid {kindColor obligation.kind};border-radius:4px;")] [
    elementWith "summary" [style "cursor:pointer;padding:.45rem .6rem;"] [
      text obligation.name,
      badge (if obligation.goal.isSome then "derived" else "pending")
        (if obligation.goal.isSome then "#98c379" else "#e06c75")
    ],
    obligationBody obligation
  ]

private def kinds : List String := ["INV", "WD", "GRD", "SIM", "THM", "WFIS", "WWD"]

private def countKind (kind : String) (obligations : List Obligation) : Nat :=
  obligations.countP (·.kind == kind)

private def countDerived (obligations : List Obligation) : Nat :=
  obligations.countP (·.goal.isSome)

private def stat (label value color : String) : Html :=
  elementWith "div" [style (s!"border-top:3px solid {color};padding:.5rem .65rem;" ++
    "border-radius:4px;background:rgba(127,127,127,.1);")] [
      elementWith "div" [style "font-size:1.35em;font-weight:700;"] [text value],
      elementWith "div" [style "font-size:.75em;opacity:.75;"] [text label]
    ]

private def summary (obligations : List Obligation) : Html :=
  elementWith "div" [style ("display:grid;grid-template-columns:repeat(3,minmax(0,1fr));" ++
    "gap:.5rem;margin:.75rem 0;")] [
      stat "total obligations" (toString obligations.length) "#4da3ff",
      stat "goals derived" (toString (countDerived obligations)) "#98c379",
      stat "obligation classes"
        (toString (kinds.countP (fun kind => countKind kind obligations > 0))) "#c678dd"
    ]

private def openAttribute (isOpen : Bool) : List (String × Json) :=
  if isOpen then [("open", .bool true)] else []

private def kindSection (kind : String) (obligations : List Obligation) (isOpen : Bool) :
    Option Html :=
  if obligations.isEmpty then
    none
  else
    some <| elementWith "details"
      (openAttribute isOpen ++ [style ("margin:.55rem 0;border:1px solid rgba(127,127,127,.3);" ++
        "border-left:4px solid {kindColor kind};border-radius:5px;")]) [
      elementWith "summary" [style "cursor:pointer;padding:.55rem .7rem;font-weight:600;"] [
        badge kind (kindColor kind),
        text s!"{kindTitle kind} · {obligations.length}"
      ],
      elementWith "div" [style "padding:0 .35rem .35rem;"]
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
  elementWith "section" [style "max-width:58rem;line-height:1.35;padding:.25rem .5rem;"] [
    elementWith "header" [style "margin-bottom:.5rem;"] [
      elementWith "h3" [style "margin:.35rem 0;font-size:1.35em;"] [
        text s!"Event-B obligations · {machine}"
      ],
      elementWith "p" [style "margin:.25rem 0;opacity:.75;"] [
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
