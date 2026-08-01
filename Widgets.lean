/-
Proof-obligation display for the Lean Infoview.

This is a separate library so the parser, POG, CLI and corpus gates do not depend on
the editor UI. The widget only renders data already produced by `EventB.POG.generate`.
-/

import EventB.DSL
import EventB.Trust
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

private def componentChildren (elem : Elem) (kind : String) : List Elem :=
  elem.children.filter (fun child => child.tag == "org.eventb.core." ++ kind)

private def componentAttr (elem : Elem) (key : String) : Option String :=
  elem.attr? ("org.eventb.core." ++ key)

private def shortTarget (target : String) : String :=
  (target.splitOn "/").getLast!

private def componentTargets (elem : Elem) (kind : String) : List String :=
  (componentChildren elem kind).filterMap (componentAttr · "target") |>.map shortTarget

private def componentNames (elem : Elem) (kind : String) : List String :=
  (componentChildren elem kind).filterMap (componentAttr · "identifier")

private def namesText (names : List String) : String :=
  names.foldl (fun acc name => if acc.isEmpty then name else acc ++ ", " ++ name) ""

private def infoLine (label value : String) : Html :=
  elementWith "p" [classes "mv1"] [
    elementWith "span" [classes "b"] [text s!"{label}: "],
    text (if value.isEmpty then "none" else value)
  ]

private def nameList (label : String) (names : List String) : Html :=
  elementWith "div" [classes "mb2"] [
    elementWith "h4" [classes "mt2 mb1 f6"] [text label],
    if names.isEmpty then
      elementWith "p" [classes "mv1 o-70"] [text "none"]
    else
      elementWith "ul" [classes "mv1 pl3"]
        (names.map fun name => element "li" [text name])
  ]

private def labelledFormula (elem : Elem) (formulaAttr : String) : Html :=
  let label := (componentAttr elem "label").getD "unnamed"
  match componentAttr elem formulaAttr with
  | some source =>
    match Formula.parse source with
    | .ok term => elementWith "div" [classes "mb2"] [
        elementWith "div" [classes "b"] [text label],
        formula term
      ]
    | .error _ => infoLine label source
  | none => infoLine label "missing formula"

private def labelledFormulas (elem : Elem) (kind formulaAttr : String) : Html :=
  let formulas := componentChildren elem kind
  elementWith "div" [classes "mb2"] [
    elementWith "h4" [classes "mt2 mb1 f6"] [text kind],
    if formulas.isEmpty then
      elementWith "p" [classes "mv1 o-70"] [text "none"]
    else
      element "div" (formulas.map (labelledFormula · formulaAttr))
  ]

private def eventCard (ev : Elem) : Html :=
  let name := (componentAttr ev "label").getD "unnamed event"
  let refinedTargets := componentTargets ev "refinesEvent"
  let parameters := componentNames ev "parameter"
  elementWith "details" [classes "mv1 ba br1"] [
    elementWith "summary" [classes "pointer pa2"] [
      text name,
      if refinedTargets.isEmpty then element "span" []
      else badge (s!"refines {namesText refinedTargets}") "purple"
    ],
    elementWith "div" [classes "pa2"] [
      infoLine "parameters" (namesText parameters),
      labelledFormulas ev "guards" "predicate",
      labelledFormulas ev "actions" "assignment"
    ]
  ]

private def eventList (elem : Elem) : Html :=
  let events := componentChildren elem "event"
  elementWith "div" [classes "mb2"] [
    elementWith "h4" [classes "mt2 mb1 f6"] [text "Events"],
    if events.isEmpty then
      elementWith "p" [classes "mv1 o-70"] [text "none"]
    else element "div" (events.map eventCard)
  ]

private def obligationStats (project : Typing.Project) (name : String) : Html :=
  let obligations := POG.generate project name
  let ledger := Trust.Ledger.ofObligations obligations
  elementWith "div" [classes "flex flex-wrap mv2"] [
    stat "proof obligations" (toString obligations.length) "blue",
    stat "goals derived" (toString (countDerived obligations)) "green",
    stat "classes" (toString (kinds.countP (fun kind => countKind kind obligations > 0))) "purple",
    stat "trust ledger" ledger.summary "orange"
  ]

private def modelPanel (kind name : String) (body : List Html) : Html :=
  elementWith "details" [classes "mv2", ("open", .bool true)] [
    elementWith "summary" [classes "pointer b"] [
      text s!"Event-B {kind} · {name}"
    ],
    elementWith "section" [classes "pa2"] body
  ]

/-- Render the declarations and proof-relevant surface of one project component. -/
def renderComponent (project : Typing.Project) (name : String) : Html :=
  match Typing.lookupComponent project name with
  | none => modelPanel "component" name [infoLine "error" "component not found"]
  | some component =>
    match component.elem with
    | .contextFile _ _ => modelPanel "context" name [
        infoLine "extends" (namesText (componentTargets component.elem "extendsContext")),
        infoLine "native theories" (namesText component.theories),
        nameList "Carrier sets" (componentNames component.elem "carrierSet"),
        nameList "Constants" (componentNames component.elem "constant"),
        labelledFormulas component.elem "Axioms" "predicate"
      ]
    | .machineFile _ _ => modelPanel "machine" name [
        infoLine "refines" (namesText (componentTargets component.elem "refinesMachine")),
        infoLine "sees" (namesText (componentTargets component.elem "seesContext")),
        infoLine "native theories" (namesText component.theories),
        nameList "Variables" (componentNames component.elem "variable"),
        labelledFormulas component.elem "Invariants" "predicate",
        labelledFormulas component.elem "Variants" "expression",
        eventList component.elem,
        obligationStats project name
      ]
    | _ => modelPanel "component" name [infoLine "error" "unsupported component kind"]

/-- Render obligations for a project component under an explicit theory environment. -/
def renderProjectIn (theory : Theory.Env) (project : Typing.Project) (machine : String) : Html :=
  let obligations := POG.generateIn theory project machine
  let ledger := Trust.Ledger.ofObligations obligations
  let first := firstKind obligations
  let sections := kinds.filterMap fun kind =>
    kindSection kind (obligations.filter (·.kind == kind)) (first == some kind)
  elementWith "details" [classes "mv2", ("open", .bool true)] [
    elementWith "summary" [classes "pointer b"] [
      text s!"Event-B proof obligations · {machine}"
    ],
    elementWith "section" [classes "pa2"] [
      elementWith "p" [classes "mv1 o-70"] [
      text "Proof-obligation explorer · expand a class, then an obligation"
      ],
      infoLine "trust" ledger.summary,
      summary obligations,
      if sections.isEmpty then element "p" [text "No obligations generated."]
      else element "div" sections
    ]
  ]

/-- Compatibility widget for projects using only the core prelude. -/
def renderProject (project : Typing.Project) (machine : String) : Html :=
  renderProjectIn Theory.empty project machine

/-- Display generated obligations without changing the ordinary text POG command. -/
syntax (name := eventbPogWidget) "#eventb_pog_widget " ident ident : command
syntax (name := eventbPogWidgetIn)
  "#eventb_pog_widget_in " ident ppSpace ident ppSpace ident : command

syntax (name := eventbModelWidget) "#eventb_model_widget " ident ident : command

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
        (hash HtmlDisplay.javascript)
        (return json% { html: $(← rpcEncode html) })
        stx
  | _ => throwUnsupportedSyntax

@[command_elab eventbPogWidgetIn]
private def elabPogWidgetIn : CommandElab := fun stx => do
  match stx with
  | `(#eventb_pog_widget_in $theory:ident $project:ident $machine:ident) => do
      let render ← `(EventB.Widgets.renderProjectIn $theory $project
        $(quote machine.getId.toString))
      let htmlX ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml
        <| ← ``(ProofWidgets.HtmlEval.eval $render)
      let html ← htmlX
      liftCoreM <| Widget.savePanelWidgetInfo
        (hash HtmlDisplay.javascript)
        (return json% { html: $(← rpcEncode html) })
        stx
  | _ => throwUnsupportedSyntax

@[command_elab eventbModelWidget]
private def elabModelWidget : CommandElab := fun stx => do
  match stx with
  | `(#eventb_model_widget $project:ident $component:ident) => do
      let render ← `(EventB.Widgets.renderComponent $project
        $(quote component.getId.toString))
      let htmlX ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml
        <| ← ``(ProofWidgets.HtmlEval.eval $render)
      let html ← htmlX
      liftCoreM <| Widget.savePanelWidgetInfo
        (hash HtmlDisplay.javascript)
        (return json% { html: $(← rpcEncode html) })
        stx
  | _ => throwUnsupportedSyntax

end EventB.Widgets
