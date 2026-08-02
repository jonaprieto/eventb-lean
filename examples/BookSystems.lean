/-
Model listings from Chapters 3, 7, 8, and 10--13, 16--17 of Modeling in Event-B.

These are intentionally small snapshots of each refinement family.  The book's export
contains many proof trees and OCR fragments; the parts here are the Event-B states and
events that those proofs discuss.  The section references are in the book export.
-/
import EventB.DSL

open EventB

/-! Chapter 3: the mechanical press controller (Sections 3.5--3.14). -/

eventb_context PressCtx where
  sets STATUS
  constants stopped working engaged disengaged door_open door_closed
  axiom axm0_1 : "STATUS = {stopped, working}"
  axiom axm0_2 : "stopped ≠ working"

eventb_machine Press0 where
  sees PressCtx
  variables motor_actuator motor_sensor
  invariant inv0_1 : "motor_actuator ∈ STATUS"
  invariant inv0_2 : "motor_sensor ∈ STATUS"
  event INITIALISATION where
    action act1 : "motor_actuator, motor_sensor ≔ stopped, stopped"
  event a_on where
    guard grd1 : "motor_actuator = stopped"
    guard grd2 : "motor_sensor = stopped"
    action act1 : "motor_actuator ≔ working"
  event a_off where
    guard grd1 : "motor_actuator = working"
    guard grd2 : "motor_sensor = working"
    action act1 : "motor_actuator ≔ stopped"
  event r_on where
    guard grd1 : "motor_sensor = stopped"
    guard grd2 : "motor_actuator = working"
    action act1 : "motor_sensor ≔ working"
  event r_off where
    guard grd1 : "motor_sensor = working"
    guard grd2 : "motor_actuator = stopped"
    action act1 : "motor_sensor ≔ stopped"

eventb_machine Press1 where
  refines Press0
  sees PressCtx
  variables motor_actuator motor_sensor start_button stop_button start_impulse stop_impulse
  invariant inv1_1 : "start_button ∈ BOOL ∧ stop_button ∈ BOOL"
  invariant inv1_2 : "start_impulse ∈ BOOL ∧ stop_impulse ∈ BOOL"
  event INITIALISATION where
    action act1 : "motor_actuator, motor_sensor ≔ stopped, stopped"
    action act2 : "start_button, stop_button ≔ FALSE, FALSE"
  event push_start where
    guard grd1 : "start_button = FALSE"
    action act1 : "start_button ≔ TRUE"
  event release_start where
    guard grd1 : "start_button = TRUE"
    action act1 : "start_button ≔ FALSE"
  event treat_push_start where
    refines a_on
    guard grd1 : "start_impulse = FALSE"
    guard grd2 : "start_button = TRUE"
    guard grd3 : "motor_actuator = stopped"
    guard grd4 : "motor_sensor = stopped"
    action act1 : "start_impulse, motor_actuator ≔ TRUE, working"
  event treat_release_start where
    guard grd1 : "start_impulse = TRUE"
    guard grd2 : "start_button = FALSE"
    action act1 : "start_impulse ≔ FALSE"

eventb_machine Press2 where
  refines Press1
  sees PressCtx
  variables motor_actuator motor_sensor clutch_actuator clutch_sensor
  invariant inv2_1 : "clutch_actuator ∈ STATUS"
  invariant inv2_2 : "clutch_sensor ∈ STATUS"
  invariant inv2_3 : "clutch_sensor = engaged ⇒ motor_sensor = working"
  event INITIALISATION where
    action act1 : "clutch_actuator, clutch_sensor ≔ disengaged, disengaged"
  event treat_start_clutch where
    guard grd1 : "clutch_actuator = disengaged"
    guard grd2 : "clutch_sensor = disengaged"
    guard grd3 : "motor_actuator = working"
    guard grd4 : "motor_sensor = working"
    action act1 : "clutch_actuator ≔ engaged"
  event treat_stop_clutch where
    guard grd1 : "clutch_actuator = engaged"
    guard grd2 : "clutch_sensor = engaged"
    action act1 : "clutch_actuator ≔ disengaged"
  event clutch_start where
    guard grd1 : "clutch_sensor = disengaged"
    guard grd2 : "clutch_actuator = engaged"
    action act1 : "clutch_sensor ≔ engaged"
  event clutch_stop where
    guard grd1 : "clutch_sensor = engaged"
    guard grd2 : "clutch_actuator = disengaged"
    action act1 : "clutch_sensor ≔ disengaged"

eventb_machine Press3 where
  refines Press2
  sees PressCtx
  variables motor_actuator motor_sensor clutch_actuator clutch_sensor door_actuator door_sensor
  invariant inv3_1 : "door_actuator ∈ STATUS"
  invariant inv3_2 : "door_sensor ∈ STATUS"
  invariant inv3_3 : "clutch_sensor = engaged ⇒ door_sensor = door_closed"
  invariant inv3_4 : "door_sensor = door_closed ⇒ motor_sensor = working"
  event INITIALISATION where
    action act1 : "door_actuator, door_sensor ≔ door_open, door_open"
  event treat_close_door where
    guard grd1 : "door_actuator = door_open"
    guard grd2 : "door_sensor = door_open"
    guard grd3 : "clutch_sensor = engaged"
    action act1 : "door_actuator ≔ door_closed"
  event treat_open_door where
    guard grd1 : "door_actuator = door_closed"
    guard grd2 : "door_sensor = door_closed"
    guard grd3 : "clutch_sensor = disengaged"
    action act1 : "door_actuator ≔ door_open"
  event door_close where
    guard grd1 : "door_sensor = door_open"
    guard grd2 : "door_actuator = door_closed"
    action act1 : "door_sensor ≔ door_closed"
  event door_open where
    guard grd1 : "door_sensor = door_closed"
    guard grd2 : "door_actuator = door_open"
    action act1 : "door_sensor ≔ door_open"

/-! Chapter 7: Simpson's four-slot asynchronous mechanism (Sections 7.4--7.9). -/

eventb_context SlotsCtx where
  sets D
  constants env cir
  axiom axm0_1 : "D ≠ ∅"

eventb_machine Slots0 where
  sees SlotsCtx
  variables mode data reading latest slot pair_w indx_w indx_r x y
  invariant inv0_1 : "mode ∈ {env, cir}"
  invariant inv0_2 : "reading ∈ {0, 1} ∧ latest ∈ {0, 1}"
  invariant inv0_3 : "slot ∈ {0, 1} → {0, 1}"
  invariant inv0_4 : "data ∈ {0, 1} → ({0, 1} → D)"
  invariant inv0_5 : "pair_w ∈ {0, 1} ∧ indx_w ∈ {0, 1} ∧ indx_r ∈ {0, 1}"
  invariant inv0_6 : "x ∈ D ∧ y ∈ D"
  event INITIALISATION where
    action act1 : "mode, reading, latest ≔ env, 1, 1"
    action act2 : "slot ≔ {0 ↦ 1, 1 ↦ 1}"
  event Writer_1 where
    any d
    guard grd1 : "mode = env"
    guard grd2 : "d ∈ D"
    action act1 : "pair_w ≔ 1 − reading"
    action act2 : "indx_w ≔ 1 − slot(pair_w)"
    action act3 : "data(pair_w)(indx_w) ≔ d"
  event Writer_2 where
    guard grd1 : "mode = env"
    action act1 : "slot(pair_w) ≔ indx_w"
  event Writer_3 where
    guard grd1 : "mode = env"
    action act1 : "latest ≔ pair_w"
  event Reader_1 where
    guard grd1 : "mode = cir"
    action act1 : "reading ≔ latest"
  event Reader_2 where
    guard grd1 : "mode = cir"
    action act1 : "indx_r ≔ slot(reading)"
  event Reader_3 where
    guard grd1 : "mode = cir"
    action act1 : "y ≔ data(reading)(indx_r)"

eventb_machine Slots1 where
  refines Slots0
  sees SlotsCtx
  variables mode data reading latest slot pair_w indx_w indx_r adr_w adr_r x y
  invariant inv1_1 : "adr_r ∈ {1, 2, 3}"
  invariant inv1_2 : "adr_w ∈ {1, 2, 3, 4, 5}"
  invariant inv1_3 : "pair_w = reading ⇒ indx_w ≠ indx_r"
  variant variant1 : "5 − adr_w"
  event Writer_1 where
    refines Writer_1
    any d
    guard grd1 : "adr_w = 1"
    guard grd2 : "d ∈ D"
    action act1 : "x ≔ d"
    action act2 : "adr_w ≔ 2"
  event Writer_2 where
    guard grd1 : "adr_w = 2"
    action act1 : "indx_w ≔ 1 − slot(pair_w)"
    action act2 : "adr_w ≔ 3"
  event Writer_3 where
    guard grd1 : "adr_w = 3"
    action act1 : "data(pair_w)(indx_w) ≔ x"
    action act2 : "adr_w ≔ 4"
  event Reader_1 where
    guard grd1 : "adr_r = 1"
    action act1 : "reading ≔ latest"
    action act2 : "adr_r ≔ 2"
  event Reader_2 where
    guard grd1 : "adr_r = 2"
    action act1 : "indx_r ≔ slot(reading)"
    action act2 : "adr_r ≔ 3"
  event Reader_3 where
    guard grd1 : "adr_r = 3"
    action act1 : "y ≔ data(reading)(indx_r)"
    action act2 : "adr_r ≔ 1"

/-! Chapter 8: synchronous circuit/environment coupling (Sections 8.1--8.5). -/

eventb_context CircuitCtx where
  sets BOOLS MODES
  constants TRUE FALSE env cir
  axiom axm0_1 : "BOOLS = {TRUE, FALSE}"
  axiom axm0_2 : "MODES = {env, cir}"
  axiom axm0_3 : "TRUE ≠ FALSE"

eventb_machine Circuit0 where
  sees CircuitCtx
  variables mode input cir_state output
  invariant inv0_1 : "mode ∈ MODES"
  invariant inv0_2 : "input ∈ BOOLS ∧ cir_state ∈ BOOLS ∧ output ∈ BOOLS"
  event INITIALISATION where
    action act1 : "mode, input, cir_state, output ≔ env, FALSE, FALSE, FALSE"
  event env_event where
    guard grd1 : "mode = env"
    action act1 : "input ≔ bool(input = FALSE)"
    action act2 : "mode ≔ cir"
  event cir_event where
    guard grd1 : "mode = cir"
    action act1 : "output ≔ bool(input ∧ cir_state)"
    action act2 : "cir_state ≔ bool(input ∨ cir_state)"
    action act3 : "mode ≔ env"

eventb_machine Circuit1 where
  refines Circuit0
  sees CircuitCtx
  variables mode input cir_state output p
  invariant inv1_1 : "p ∈ BOOLS"
  invariant inv1_2 : "output = bool(input ∧ p)"
  event INITIALISATION where
    action act1 : "p ≔ FALSE"
  event cir_event where
    refines cir_event
    guard grd1 : "mode = cir"
    action act1 : "p ≔ bool(input ∧ p)"
    action act2 : "output ≔ p"
    action act3 : "mode ≔ env"

/-! Chapter 10: leader election on a ring (Sections 10.2--10.5). -/

eventb_context RingCtx where
  sets N
  constants next itvr
  axiom axm0_1 : "finite(N)"
  axiom axm0_2 : "N ≠ ∅"
  axiom axm1_1 : "next ∈ N → N"
  axiom axm1_2 : "itvr ∈ N → (N → ℙ(N))"
  axiom theorem axm1_3 : "∀x · x ∈ N ⇒ itvr(x)(x) = N"

eventb_machine Ring0 where
  sees RingCtx
  variables w
  invariant inv0_1 : "w ∈ N"
  event INITIALISATION where
    action act1 : "w ≔ max(N)"
  event elect where
    action act1 : "w ≔ max(N)"

eventb_machine Ring1 where
  refines Ring0
  sees RingCtx
  variables w a
  invariant inv1_1 : "a ∈ N ⇸ N"
  invariant inv1_2 : "∀x · x ∈ dom(a) ⇒ x = max(itvr(x)(next∼(a(x))))"
  event INITIALISATION where
    action act1 : "a ≔ ∅"
  event elect where
    refines elect
    any x
    guard grd1 : "x ∈ dom(a)"
    guard grd2 : "x = a(x)"
    action act1 : "w ≔ x"
  event accept where
    any x
    guard grd1 : "x ∈ dom(a)"
    guard grd2 : "a(x) < x"
    action act1 : "a(x) ≔ next(a(x))"
  event reject where
    any x
    guard grd1 : "x ∈ dom(a)"
    guard grd2 : "x < a(x)"
    action act1 : "a ≔ {x} ◁ a"

/-! Chapter 11: synchronizing a tree-shaped network (Sections 11.2--11.6). -/

eventb_context TreeCtx where
  sets N
  constants r L f
  axiom axm0_1 : "finite(N)"
  axiom axm1_1 : "r ∈ N"
  axiom axm1_2 : "L ⊆ N"
  axiom axm1_3 : "f ∈ N ∖ {r} → N ∖ L"

eventb_machine Tree0 where
  sees TreeCtx
  variables c
  invariant inv0_1 : "c ∈ N → ℕ"
  invariant inv0_2 : "∀x,y · x ∈ N ∧ y ∈ N ⇒ c(x) ≤ c(y) + 1"
  event INITIALISATION where
    action act1 : "c ≔ N × {0}"
  event increment where
    any n
    guard grd1 : "n ∈ N"
    guard grd2 : "∀m · m ∈ N ⇒ c(n) ≤ c(m)"
    action act1 : "c(n) ≔ c(n) + 1"

eventb_machine Tree1 where
  refines Tree0
  sees TreeCtx
  variables c
  invariant inv1_1 : "∀m · m ∈ N ∖ {r} ⇒ c(f(m)) ≤ c(m)"
  invariant theorem thm1_1 : "∀m · m ∈ N ⇒ c(r) ≤ c(m)"
  event increment where
    refines increment
    any n
    guard grd1 : "n ∈ N"
    guard grd2 : "n = r ∨ c(n) = c(r)"
    action act1 : "c(n) ≔ c(n) + 1"
  event ascending where
    extends increment
    any n
    guard grd1 : "n ∈ N ∖ {r}"
    guard grd2 : "c(n) = c(f(n))"
    action act1 : "c(n) ≔ c(n) + 1"

/-! Chapter 12: routing algorithm for a mobile agent (Sections 12.2--12.5). -/

eventb_context AgentCtx where
  sets S M
  constants next
  axiom axm0_1 : "next ∈ S → S"

eventb_machine Agent0 where
  sees AgentCtx
  variables agt pos msg delivered
  invariant inv0_1 : "agt ∈ S"
  invariant inv0_2 : "pos ∈ S"
  invariant inv0_3 : "msg ∈ M"
  invariant inv0_4 : "delivered ⊆ M"
  event INITIALISATION where
    action act1 : "agt, pos ≔ ∅, ∅"
    action act2 : "delivered ≔ ∅"
  event rcv_agt where
    any m
    guard grd1 : "m ∈ M"
    action act1 : "agt ≔ agt ∪ {m}"
  event fwd_msg where
    guard grd1 : "agt ≠ ∅"
    action act1 : "pos ≔ next(pos)"
  event dlv_msg where
    guard grd1 : "msg ∈ agt"
    action act1 : "delivered ≔ delivered ∪ {msg}"

/-! Chapter 13: leader election on a connected graph (Sections 13.1--13.6). -/

eventb_context GraphCtx where
  sets N
  constants edges
  axiom axm0_1 : "finite(N)"
  axiom axm0_2 : "edges ∈ N ↔ N"

eventb_machine Graph0 where
  sees GraphCtx
  variables l
  invariant inv0_1 : "l ∈ N"
  event INITIALISATION where
    action act1 : "l ≔ ∅"
  event elect where
    any x
    guard grd1 : "x ∈ N"
    action act1 : "l ≔ x"

eventb_machine Graph1 where
  refines Graph0
  sees GraphCtx
  variables l n m c bm
  invariant inv1_1 : "n ⊆ N"
  invariant inv1_2 : "m ∈ N ⇸ N"
  invariant inv1_3 : "c ⊆ edges"
  event send_msg where
    any x
    guard grd1 : "x ∈ n"
    action act1 : "m ≔ m ∪ {x ↦ l}"
  event progress where
    any x y
    guard grd1 : "x ↦ y ∈ m"
    action act1 : "m ≔ {x} ◁ m"
  event discover_contention where
    guard grd1 : "m ≠ ∅"
    action act1 : "c ≔ c ∪ m"
  event solve_contention where
    any x y
    guard grd1 : "c = {x ↦ y, y ↦ x}"
    action act1 : "c ≔ ∅"

/-! Chapter 16: location access controller (Sections 16.3--16.6). -/

eventb_context AccessCtx where
  sets PERSON LOCATION
  constants auth
  axiom axm0_1 : "auth ∈ PERSON ↔ LOCATION"

eventb_machine Access0 where
  sees AccessCtx
  variables inside
  invariant inv0_1 : "inside ⊆ auth"
  invariant inv0_2 : "inside ∈ PERSON ↔ LOCATION"
  event INITIALISATION where
    action act1 : "inside ≔ ∅"
  event enter where
    any p l
    guard grd1 : "p ↦ l ∈ auth"
    guard grd2 : "p ↦ l ∉ inside"
    action act1 : "inside ≔ inside ∪ {p ↦ l}"
  event leave where
    any p l
    guard grd1 : "p ↦ l ∈ inside"
    action act1 : "inside ≔ {p ↦ l} ◁ inside"

eventb_machine Access1 where
  refines Access0
  sees AccessCtx
  variables inside green red
  invariant inv1_1 : "green ⊆ PERSON × LOCATION"
  invariant inv1_2 : "red ⊆ PERSON × LOCATION"
  event card_read where
    any p l
    guard grd1 : "p ↦ l ∈ auth"
    action act1 : "green ≔ green ∪ {p ↦ l}"
  event passage where
    any p l
    guard grd1 : "p ↦ l ∈ green"
    action act1 : "inside ≔ inside ∪ {p ↦ l}"

/-! Chapter 17: train system (Sections 17.3--17.7). -/

eventb_context TrainCtx where
  sets B R S
  constants fst lst nxt
  axiom axm0_1 : "fst ∈ R → B"
  axiom axm0_2 : "lst ∈ R → B"
  axiom axm0_3 : "nxt ∈ B → B"

eventb_machine Train0 where
  sees TrainCtx
  variables resrt frm occ lbt rsrtbl resbl
  invariant inv0_1 : "resrt ⊆ R"
  invariant inv0_2 : "frm ⊆ R"
  invariant inv0_3 : "occ ⊆ B"
  invariant inv0_4 : "lbt ⊆ B"
  invariant inv0_5 : "rsrtbl ∈ B ⇸ R"
  invariant inv0_6 : "resbl ⊆ B"
  event INITIALISATION where
    action act1 : "resrt, frm, occ, lbt, resbl ≔ ∅, ∅, ∅, ∅, ∅"
  event route_reservation where
    any r
    guard grd1 : "r ∈ R ∖ resrt"
    action act1 : "resrt ≔ resrt ∪ {r}"
  event route_formation where
    any r
    guard grd1 : "r ∈ resrt ∖ frm"
    action act1 : "frm ≔ frm ∪ {r}"
  event FRONT_MOVE_1 where
    any r
    guard grd1 : "r ∈ frm"
    guard grd2 : "fst(r) ∈ resbl ∖ occ"
    action act1 : "occ, lbt ≔ occ ∪ {fst(r)}, lbt ∪ {fst(r)}"
  event BACK_MOVE where
    any b
    guard grd1 : "b ∈ lbt"
    guard grd2 : "b ∉ dom(rsrtbl)"
    action act1 : "occ ≔ occ ∖ {b}"

eventb_machine Train1 where
  refines Train0
  sees TrainCtx
  variables resrt frm occ lbt rsrtbl resbl rdy
  invariant inv1_1 : "rdy ⊆ frm"
  invariant inv1_2 : "∀r · r ∈ rdy ⇒ rsrtbl∼[{r}] ⊆ resbl"
  event route_formation where
    refines route_formation
    any r
    guard grd1 : "r ∈ resrt ∖ frm"
    action act1 : "frm, rdy ≔ frm ∪ {r}, rdy ∪ {r}"
  event FRONT_MOVE_1 where
    refines FRONT_MOVE_1
    any r
    guard grd1 : "r ∈ rdy"
    action act1 : "occ, lbt, rdy ≔ occ ∪ {fst(r)}, lbt ∪ {fst(r)}, rdy ∖ {r}"

def systemsProject : Typing.Project :=
  [ { name := "PressCtx", elem := PressCtx }
  , { name := "Press0", elem := Press0 }
  , { name := "Press1", elem := Press1 }
  , { name := "Press2", elem := Press2 }
  , { name := "Press3", elem := Press3 }
  , { name := "SlotsCtx", elem := SlotsCtx }
  , { name := "Slots0", elem := Slots0 }
  , { name := "Slots1", elem := Slots1 }
  , { name := "CircuitCtx", elem := CircuitCtx }
  , { name := "Circuit0", elem := Circuit0 }
  , { name := "Circuit1", elem := Circuit1 }
  , { name := "RingCtx", elem := RingCtx }
  , { name := "Ring0", elem := Ring0 }
  , { name := "Ring1", elem := Ring1 }
  , { name := "TreeCtx", elem := TreeCtx }
  , { name := "Tree0", elem := Tree0 }
  , { name := "Tree1", elem := Tree1 }
  , { name := "AgentCtx", elem := AgentCtx }
  , { name := "Agent0", elem := Agent0 }
  , { name := "GraphCtx", elem := GraphCtx }
  , { name := "Graph0", elem := Graph0 }
  , { name := "Graph1", elem := Graph1 }
  , { name := "AccessCtx", elem := AccessCtx }
  , { name := "Access0", elem := Access0 }
  , { name := "Access1", elem := Access1 }
  , { name := "TrainCtx", elem := TrainCtx }
  , { name := "Train0", elem := Train0 }
  , { name := "Train1", elem := Train1 } ]

private def hasPO (machine name : String) : Bool :=
  (POG.generate systemsProject machine).any (·.name == name)

#guard hasPO "Press0" "a_on/inv0_1/INV"
#guard hasPO "Slots0" "Writer_1/inv0_5/INV"
#guard hasPO "Circuit0" "env_event/inv0_1/INV"
#guard hasPO "Ring1" "elect/act1/SIM"
#guard hasPO "Tree1" "thm1_1/THM"
#guard hasPO "Graph1" "send_msg/inv1_2/INV"
#guard hasPO "Access0" "enter/inv0_1/INV"
#guard hasPO "Train1" "route_formation/act1/SIM"

private def pressGoal (name : String) : Option String :=
  (POG.generate systemsProject "Press0").find? (·.name == name) |>.bind
    (fun obligation => obligation.goal.map Formula.print)

private def pressHypotheses (name : String) : Option (List String) :=
  (POG.generate systemsProject "Press0").find? (·.name == name) |>.map
    (fun obligation => obligation.hyps.map Formula.print)

#guard pressGoal "a_on/inv0_1/INV" == some "(working ∈ STATUS)"
#guard pressHypotheses "a_on/inv0_1/INV" == some
  ["(STATUS = {stopped, working})", "(stopped ≠ working)",
   "(motor_actuator ∈ STATUS)", "(motor_sensor ∈ STATUS)",
   "(motor_actuator = stopped)", "(motor_sensor = stopped)"]
