import EventB.DSL
import Widgets

open EventB

/-!
A self-contained Infoview demo: a small bridge controller and one refinement.

Open this file in VS Code, restart the Lean server after changing widget code, and
inspect the expandable obligation dashboard produced by the final command.
-/

eventb_context WidgetCtx where
  constants LIMIT
  axiom lim_nat : "LIMIT ∈ ℕ"
  axiom lim_positive : "0 < LIMIT"

eventb_machine BridgeBase where
  sees WidgetCtx
  variables cars
  invariant inv0_1 : "cars ∈ ℕ"
  invariant inv0_2 : "cars ≤ LIMIT"
  event INITIALISATION where
    action act1 : "cars ≔ 0"
  event enter where
    guard grd1 : "cars < LIMIT"
    action act1 : "cars ≔ cars + 1"
  event leave where
    guard grd1 : "0 < cars"
    action act1 : "cars ≔ cars − 1"

eventb_machine BridgeController where
  refines BridgeBase
  sees WidgetCtx
  variables cars gate
  invariant inv1_1 : "gate ∈ BOOL"
  invariant inv1_2 : "gate = TRUE ⇒ cars < LIMIT"
  event INITIALISATION where
    action act1 : "cars ≔ 0"
    action act2 : "gate ≔ FALSE"
  event enter where
    refines enter
    guard grd1 : "gate = FALSE"
    action act1 : "cars ≔ cars + 1"
    action act2 : "gate ≔ TRUE"
  event leave where
    refines leave
    guard grd1 : "gate = TRUE"
    action act1 : "cars ≔ cars − 1"
    action act2 : "gate ≔ FALSE"

def widgetProject : Typing.Project :=
  [ { name := "WidgetCtx", elem := WidgetCtx }
  , { name := "BridgeBase", elem := BridgeBase }
  , { name := "BridgeController", elem := BridgeController } ]

#guard (POG.generate widgetProject "BridgeController").isEmpty == false

#eventb_pog_widget widgetProject BridgeController
