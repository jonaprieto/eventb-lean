import EventB.DSL
import EventB.Trust.Replay
import Widgets

open EventB
open Lean Elab Command Meta

/-!
A self-contained Infoview demo: a small bridge controller and one refinement.

Open this file in VS Code, restart the Lean server after changing widget code, and
inspect the expandable obligation dashboard produced by the final command. The
ledger below contains kernel-replayed proofs for this deliberately small model, so
the panel demonstrates both generated obligations and trusted evidence.
-/

eventb_context WidgetCtx where
  constants LIMIT
  axiom lim_nat : LIMIT ∈ ℕ
  axiom lim_positive : 0 < LIMIT

eventb_machine BridgeBase where
  sees WidgetCtx
  variables cars

  invariant inv0_1 : cars ∈ ℕ
  invariant inv0_2 : cars ≤ LIMIT

  event INITIALISATION where
    action act1 : cars := 0

  event enter where
    guard grd1 : cars < LIMIT
    action act1 : cars := cars + 1

  event leave where
    guard grd1 : 0 < cars
    action act1 : cars := cars - 1

eventb_machine BridgeController where
  refines BridgeBase
  sees WidgetCtx
  variables cars gate

  invariant inv1_1 : gate ∈ BOOL
  invariant inv1_2 : gate = TRUE ⇒ cars < LIMIT

  event INITIALISATION where
    action act1 : cars := 0
    action act2 : gate := FALSE

  event enter where
    refines enter
    guard grd1 : gate = FALSE ∧ cars + 1 < LIMIT
    action act1 : cars := cars + 1
    action act2 : gate := TRUE

  event leave where
    refines leave
    guard grd1 : gate = TRUE ∧ 0 < cars
    action act1 : cars := cars - 1
    action act2 : gate := FALSE

def widgetProject : Typing.Project :=
  [ { name := "WidgetCtx", elem := WidgetCtx }
  , { name := "BridgeBase", elem := BridgeBase }
  , { name := "BridgeController", elem := BridgeController } ]

namespace WidgetProofs

theorem initialInv1 (limit _cars : Int) (_gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) : True := by
  trivial

theorem initialInv2 (limit _cars : Int) (_gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) : false = true → 0 < limit := by
  intro contradiction
  cases contradiction

theorem initialSim (limit _cars : Int) (_gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) : (0 : Int) = 0 := by
  rfl

theorem enterInv1 (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = false ∧ cars + 1 < limit) : True := by
  trivial

theorem enterInv2 (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = false ∧ cars + 1 < limit) :
    true = true → cars + 1 < limit := by
  intro _
  exact ‹gate = false ∧ cars + 1 < limit›.2

theorem enterGuard (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (condition : gate = false ∧ cars + 1 < limit) : cars < limit := by
  omega

theorem enterSim (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = false ∧ cars + 1 < limit) :
    cars + 1 = cars + 1 := by
  rfl

theorem leaveInv1 (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = true ∧ 0 < cars) : True := by
  trivial

theorem leaveInv2 (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = true ∧ 0 < cars) :
    false = true → cars - 1 < limit := by
  intro contradiction
  cases contradiction

theorem leaveGuard (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (condition : gate = true ∧ 0 < cars) : 0 < cars := by
  exact condition.2

theorem leaveSim (limit cars : Int) (gate : Bool)
    (_ : 0 ≤ limit) (_ : 0 < limit) (_ : 0 ≤ cars) (_ : cars ≤ limit)
    (_ : True) (_ : gate = true → cars < limit)
    (_ : gate = true ∧ 0 < cars) :
    cars - 1 = cars - 1 := by
  rfl

end WidgetProofs

private def widgetProofs : List (String × String) :=
  [ ("INITIALISATION/inv1_1/INV", "WidgetProofs.initialInv1")
  , ("INITIALISATION/inv1_2/INV", "WidgetProofs.initialInv2")
  , ("INITIALISATION/act1/SIM", "WidgetProofs.initialSim")
  , ("enter/inv1_1/INV", "WidgetProofs.enterInv1")
  , ("enter/inv1_2/INV", "WidgetProofs.enterInv2")
  , ("enter/grd1/GRD", "WidgetProofs.enterGuard")
  , ("enter/act1/SIM", "WidgetProofs.enterSim")
  , ("leave/inv1_1/INV", "WidgetProofs.leaveInv1")
  , ("leave/inv1_2/INV", "WidgetProofs.leaveInv2")
  , ("leave/grd1/GRD", "WidgetProofs.leaveGuard")
  , ("leave/act1/SIM", "WidgetProofs.leaveSim") ]

private def widgetAxioms (declaration : String) : List String :=
  if declaration == "WidgetProofs.enterGuard" then ["Quot.sound", "propext"] else []

private def attachWidgetProof (ledger : Trust.Ledger)
    (obligations : List POG.Obligation) (name declaration : String) : Trust.Ledger :=
  match obligations.find? (·.name == name) with
  | none => ledger
  | some obligation =>
      match ledger.attach obligation (.kernel declaration (widgetAxioms declaration)) with
      | .ok updated => updated
      | .error _ => ledger

def widgetLedger : Trust.Ledger :=
  let obligations := POG.generate widgetProject "BridgeController"
  let initial := Trust.Ledger.ofObligations obligations
  widgetProofs.foldl (fun ledger (name, declaration) =>
    attachWidgetProof ledger obligations name declaration) initial

private def validateWidgetProofs (limit cars gate : Expr) : MetaM Unit := do
  let context : Embedding.KernelContext :=
    { bindings :=
        [{ name := "LIMIT", ty := .int, value := limit }
        , { name := "cars", ty := .int, value := cars }
        , { name := "gate", ty := .bool, value := gate }] }
  let obligations := POG.generate widgetProject "BridgeController"
  for entry in widgetLedger.entries do
    if entry.mode == .kernel then
      let some obligation := obligations.find? (·.name == entry.obligation) | throwError
        s!"missing WidgetDemo obligation `{entry.obligation}`"
      let report ← Trust.Replay.validateEntry context obligation entry
      unless report.replayed do
        throwError s!"WidgetDemo proof `{entry.obligation}` was not replayed"

private meta def checkWidgetProofs : TermElabM Unit := do
  let intType := mkConst ``Int
  let boolType := mkConst ``Bool
  liftMetaM <| withLocalDeclD `LIMIT intType fun limit =>
    withLocalDeclD `cars intType fun cars =>
      withLocalDeclD `gate boolType fun gate =>
        validateWidgetProofs limit cars gate

syntax (name := widgetProofChecks) "#eventb_widget_proof_checks" : command

@[command_elab widgetProofChecks]
private def elabWidgetProofChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_widget_proof_checks) => liftTermElabM checkWidgetProofs
  | _ => throwUnsupportedSyntax

#eventb_widget_proof_checks

#guard (POG.generate widgetProject "BridgeController").isEmpty == false
#guard widgetLedger.count .unproved == 0
#guard ((POG.generate widgetProject "BridgeController").map (·.name)
  |>.countP (· == "enter/act1/SIM")) == 1
#guard ((POG.generate widgetProject "BridgeController").map (·.name)
  |>.countP (· == "enter/grd1/GRD")) == 1

#eventb_model_widget widgetProject WidgetCtx
#eventb_model_widget widgetProject BridgeController
#eventb_pog_widget_with_ledger widgetProject BridgeController widgetLedger
