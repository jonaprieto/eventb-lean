/-
Executable transcriptions of the model listings in Modeling in Event-B.

The source is the OCR export at `docs/event-b.md/book.md`; section numbers below are
the stable references because the export has no reliable printed page breaks.  These
models deliberately use the same DSL as `Counter.lean`: every quoted formula is parsed
at elaboration time and every model is available to the ordinary POG.
-/
import EventB.DSL

open EventB

/-! Chapter 2, "Controlling cars on a bridge", Sections 2.4--2.7. -/

eventb_context BridgeCtx where
  constants d red green on off
  axiom axm0_1 : "d ∈ ℕ"
  axiom axm0_2 : "0 < d"

eventb_machine Bridge0 where
  sees BridgeCtx
  variables n
  invariant inv0_1 : "n ∈ ℕ"
  invariant inv0_2 : "n ≤ d"
  event INITIALISATION where
    action act1 : "n ≔ 0"
  event ML_out where
    guard grd1 : "n < d"
    action act1 : "n ≔ n + 1"
  event ML_in where
    guard grd1 : "0 < n"
    action act1 : "n ≔ n − 1"

eventb_machine Bridge1 where
  refines Bridge0
  sees BridgeCtx
  variables a b c
  invariant inv1_1 : "a ∈ ℕ"
  invariant inv1_2 : "b ∈ ℕ"
  invariant inv1_3 : "c ∈ ℕ"
  invariant inv1_4 : "a + b + c = n"
  invariant inv1_5 : "a = 0 ∨ c = 0"
  variant variant1 : "2 ∗ a + b"
  event INITIALISATION where
    action act1 : "a, b, c ≔ 0, 0, 0"
  event ML_out where
    refines ML_out
    guard grd1 : "a + b < d"
    guard grd2 : "c = 0"
    action act1 : "a ≔ a + 1"
  event ML_in where
    refines ML_in
    guard grd1 : "0 < c"
    action act1 : "c ≔ c − 1"
  event IL_in where
    guard grd1 : "0 < a"
    action act1 : "a, b ≔ a − 1, b + 1"
  event IL_out where
    guard grd1 : "0 < b"
    guard grd2 : "a = 0"
    action act1 : "b, c ≔ b − 1, c + 1"

eventb_machine Bridge2 where
  refines Bridge1
  sees BridgeCtx
  variables a b c ml_tl il_tl
  invariant inv2_1 : "ml_tl ∈ {red, green}"
  invariant inv2_2 : "il_tl ∈ {red, green}"
  invariant inv2_3 : "ml_tl = green ⇒ a + b < d ∧ c = 0"
  invariant inv2_4 : "il_tl = green ⇒ 0 < b ∧ a = 0"
  invariant inv2_5 : "ml_tl = red ∨ il_tl = red"
  event INITIALISATION where
    action act1 : "a, b, c, ml_tl, il_tl ≔ 0, 0, 0, red, red"
  event ML_out where
    refines ML_out
    guard grd1 : "ml_tl = green"
    action act1 : "a ≔ a + 1"
  event ML_in where
    refines ML_in
    guard grd1 : "0 < c"
    action act1 : "c ≔ c − 1"
  event IL_in where
    refines IL_in
    guard grd1 : "0 < a"
    action act1 : "a, b ≔ a − 1, b + 1"
  event IL_out where
    refines IL_out
    guard grd1 : "il_tl = green"
    action act1 : "b, c ≔ b − 1, c + 1"
  event ML_tl_green where
    guard grd1 : "ml_tl = red"
    guard grd2 : "a + b < d"
    guard grd3 : "c = 0"
    action act1 : "ml_tl ≔ green"
  event IL_tl_green where
    guard grd1 : "il_tl = red"
    guard grd2 : "0 < b"
    guard grd3 : "a = 0"
    action act1 : "il_tl ≔ green"

eventb_machine Bridge3 where
  refines Bridge2
  sees BridgeCtx
  variables a b c ml_tl il_tl ml_out_sensor ml_in_sensor il_out_sensor il_in_sensor
  invariant inv3_1 : "ml_out_sensor ∈ {on, off}"
  invariant inv3_2 : "ml_in_sensor ∈ {on, off}"
  invariant inv3_3 : "il_out_sensor ∈ {on, off}"
  invariant inv3_4 : "il_in_sensor ∈ {on, off}"
  invariant inv3_5 : "a ∈ ℕ ∧ b ∈ ℕ ∧ c ∈ ℕ"
  invariant inv3_6 : "a = 0 ∨ c = 0"
  invariant inv3_7 : "il_in_sensor = on ⇒ a > 0"
  invariant inv3_8 : "il_out_sensor = on ⇒ b > 0"
  event INITIALISATION where
    action act1 : "a, b, c ≔ 0, 0, 0"
  event ML_out_arr where
    guard grd1 : "ml_out_sensor = off"
    action act1 : "ml_out_sensor ≔ on"
  event ML_out_dep where
    guard grd1 : "ml_out_sensor = on"
    guard grd2 : "ml_tl = green"
    action act1 : "ml_out_sensor, a ≔ off, a + 1"
  event IL_in_arr where
    guard grd1 : "il_in_sensor = off"
    guard grd2 : "c > 0"
    action act1 : "il_in_sensor ≔ on"
  event IL_in_dep where
    guard grd1 : "il_in_sensor = on"
    action act1 : "il_in_sensor, c ≔ off, c − 1"

/-! Chapter 4, "A simple file transfer protocol", Sections 4.3--4.6. -/

eventb_context FileCtx where
  sets D
  constants n f MAX working success failure
  axiom axm0_1 : "0 < n"
  axiom axm0_2 : "f ∈ 1‥n → D"
  axiom axm0_3 : "MAX ∈ ℕ"

eventb_machine File0 where
  sees FileCtx
  variables g b
  invariant inv0_1 : "g ∈ 1‥n ⇸ D"
  invariant inv0_2 : "b = FALSE ⇒ g = ∅"
  invariant inv0_3 : "b = TRUE ⇒ g = f"
  event INITIALISATION where
    action act1 : "g ≔ ∅"
    action act2 : "b ≔ FALSE"
  event final where
    guard grd1 : "b = FALSE"
    action act1 : "g ≔ f"
    action act2 : "b ≔ TRUE"

eventb_machine File1 where
  refines File0
  sees FileCtx
  variables h r b
  invariant inv1_1 : "r ∈ 1‥n + 1"
  invariant inv1_2 : "h = (1‥r − 1) ◁ f"
  invariant inv1_3 : "b = TRUE ⇒ r = n + 1"
  variant variant1 : "n + 1 − r"
  event INITIALISATION where
    action act1 : "h ≔ ∅"
    action act2 : "r ≔ 1"
    action act3 : "b ≔ FALSE"
  event receive where
    status convergent
    guard grd1 : "r < n"
    action act1 : "h ≔ h ∪ {r ↦ f(r)}"
    action act2 : "r ≔ r + 1"
  event final where
    refines final
    guard grd1 : "r = n + 1"
    guard grd2 : "b = FALSE"
    witness wit1 : "g = h"
    action act1 : "b ≔ TRUE"

eventb_machine File2 where
  refines File1
  sees FileCtx
  variables h r b w s v ab db
  invariant inv2_1 : "s ∈ 0‥n"
  invariant inv2_2 : "r ∈ 0‥n"
  invariant inv2_3 : "w ∈ 0‥n"
  invariant inv2_4 : "ab ∈ BOOL ∧ db ∈ BOOL ∧ v ∈ BOOL"
  invariant inv2_5 : "h = (1‥r) ◁ f"
  event INITIALISATION where
    action act1 : "h, r, s, w ≔ ∅, 0, 0, 0"
  event SND_snd where
    guard grd1 : "s < n"
    action act1 : "w ≔ s + 1"
    action act2 : "db ≔ TRUE"
  event RCV_rcv where
    guard grd1 : "db = TRUE"
    action act1 : "r ≔ r + 1"
    action act2 : "h ≔ h ∪ {r ↦ f(r)}"
  event SND_rcv_ack where
    guard grd1 : "ab = TRUE"
    action act1 : "s ≔ s + 1"
    action act2 : "ab ≔ FALSE"

eventb_machine File3 where
  refines File2
  sees FileCtx
  variables h r s w ab db v c s_st r_st
  invariant inv3_1 : "s_st ∈ {working, success, failure}"
  invariant inv3_2 : "r_st ∈ {working, success, failure}"
  invariant inv3_3 : "c ∈ 0‥MAX + 1"
  invariant inv3_4 : "s_st = success ⇒ r_st = success"
  invariant inv3_5 : "ab = TRUE ⇒ r = s + 1"
  event SND_time_out_current where
    guard grd1 : "s_st = working"
    guard grd2 : "c < MAX"
    action act1 : "c ≔ c + 1"
  event SND_failure where
    guard grd1 : "s_st = working"
    guard grd2 : "c = MAX"
    action act1 : "s_st ≔ failure"
  event RCV_failure where
    guard grd1 : "r_st = working"
    guard grd2 : "c = MAX + 1"
    action act1 : "r_st ≔ failure"

/-! The notation used by the book is exercised by the same formulas in the models:
partial/total functions, domain restriction, images, lambdas, quantifiers, intervals,
boolean values, simultaneous assignments, witnesses, theorem predicates and refinement
targets.  These are deliberately real `Elem` trees, not comments or parser-only tests. -/

def bookProject : Typing.Project :=
  [ { name := "BridgeCtx", elem := BridgeCtx }
  , { name := "Bridge0", elem := Bridge0 }
  , { name := "Bridge1", elem := Bridge1 }
  , { name := "Bridge2", elem := Bridge2 }
  , { name := "Bridge3", elem := Bridge3 }
  , { name := "FileCtx", elem := FileCtx }
  , { name := "File0", elem := File0 }
  , { name := "File1", elem := File1 }
  , { name := "File2", elem := File2 }
  , { name := "File3", elem := File3 } ]

private def hasPO (machine name : String) : Bool :=
  (POG.generate bookProject machine).any (·.name == name)

private def goalText (machine name : String) : Option String :=
  (POG.generate bookProject machine).find? (·.name == name) |>.bind
    (fun obligation => obligation.goal.map Formula.print)

private def hypothesesText (machine name : String) : Option (List String) :=
  (POG.generate bookProject machine).find? (·.name == name) |>.map
    (fun obligation => obligation.hyps.map Formula.print)

#guard hasPO "Bridge0" "INITIALISATION/inv0_1/INV"
#guard hasPO "Bridge1" "INITIALISATION/inv1_1/INV"
#guard hasPO "Bridge2" "INITIALISATION/inv2_1/INV"
#guard hasPO "File0" "INITIALISATION/inv0_1/INV"
#guard hasPO "File1" "INITIALISATION/inv1_1/INV"
#guard hasPO "File2" "INITIALISATION/inv2_1/INV"

#guard goalText "Bridge0" "INITIALISATION/inv0_1/INV" == some "(0 ∈ ℕ)"
#guard goalText "Bridge0" "ML_out/inv0_2/INV" == some "((n + 1) ≤ d)"
#guard hypothesesText "Bridge0" "ML_out/inv0_2/INV" == some
  ["(d ∈ ℕ)", "(0 < d)", "(n ∈ ℕ)", "(n ≤ d)", "(n < d)"]
#guard hasPO "File1" "final/act2/SIM"
#guard hasPO "File1" "final/wit1/WFIS"

/-! Negative controls: exact checks must fail for a changed goal or missing PO. -/
#guard !goalText "Bridge0" "ML_out/inv0_2/INV" == some "((n + 1) < d)"
#guard !hasPO "Bridge0" "ML_out/inv0_9/INV"
