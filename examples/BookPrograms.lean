/-
Notation and sequential-program examples from Chapters 5, 9, and 15 of Modeling in
Event-B.  The examples are normalized from the OCR export, but retain the book's
labels and mathematical constructs so they exercise the actual parser and POG.
-/
import EventB.DSL

open EventB

/-! Chapter 5: the notation and proof-obligation running example (Sections 5.1--5.2). -/

eventb_context NotationCtx where
  sets D
  constants n f
  axiom axm0_1 : "0 < n"
  axiom axm0_2 : "f ∈ 1‥n → D"
  axiom theorem axm0_3 : "∀x · x ∈ 1‥n ⇒ x ∈ ℕ"

eventb_machine NotationMachine where
  sees NotationCtx
  variables x y z g
  invariant inv0_1 : "x ∈ ℕ"
  invariant inv0_2 : "y ∈ ℕ"
  invariant inv0_3 : "g ∈ 1‥n ⇸ D"
  event INITIALISATION where
    action act1 : "x, y ≔ 0, 0"
  event deterministic where
    guard grd1 : "x < n"
    action act1 : "x ≔ x + z"
  event function_update where
    any i v
    guard grd1 : "i ∈ 1‥n"
    guard grd2 : "v ∈ D"
    action act1 : "g(i) ≔ v"
  event nondeterministic_value where
    guard grd1 : "x ∈ ℕ"
    action act1 : "x :∈ 0‥n"
  event nondeterministic_relation where
    action act1 : "x :∣ x' = y' ∧ y' = x' + z"
  event witness_example where
    any i v
    guard grd1 : "v ∈ D"
    witness wit1 : "v = f(i)"
    action act1 : "y ≔ y + 1"

/-! Chapter 9: mathematical language and advanced data structures (Sections 9.2--9.7). -/

eventb_context MathCtx where
  sets S V
  constants r f n p cl
  axiom axm0_1 : "r ∈ S ↔ S"
  axiom axm0_2 : "f ∈ V"
  axiom axm0_3 : "n ∈ V → V"
  axiom axm0_4 : "n ∈ V ⇸ V"
  axiom axm0_5 : "p ∈ V → ℙ(V)"
  axiom axm0_6 : "r = λx · x ↦ x"
  axiom theorem axm0_7 : "∀x · x ∈ V ⇒ x ∈ V"
  axiom axm0_8 : "finite(V)"
  axiom axm0_9 : "BOOL = {TRUE, FALSE}"

eventb_machine MathMachine where
  sees MathCtx
  variables t u
  invariant inv0_1 : "t ∈ V"
  invariant inv0_2 : "u ∈ ℙ(V)"
  invariant inv0_3 : "cl(r) ; cl(r) ⊆ cl(r)"
  event INITIALISATION where
    action act1 : "t, u ≔ f, {f}"
  event closure_step where
    guard grd1 : "t ∈ u"
    action act1 : "u ≔ u ∪ n[u]"

/-! Chapter 15.2--15.3: a small program developed from a specification. -/

eventb_machine SimpleProgram where
  sees MathCtx
  variables x y
  invariant inv0_1 : "x ∈ ℕ"
  invariant inv0_2 : "y ∈ ℕ"
  event INITIALISATION where
    action act1 : "x, y ≔ 0, 0"
  event final where
    guard grd1 : "x = y"
  event progress where
    status anticipated
    guard grd1 : "x < y"
    action act1 : "x ≔ x + 1"
  event progress_converged where
    status convergent
    guard grd1 : "x < y"
    action act1 : "x ≔ x + 1"

/-! Chapter 15.4: binary search in a sorted array. -/

eventb_context SearchCtx where
  sets D
  constants n f v
  axiom axm0_1 : "n ∈ ℕ"
  axiom axm0_2 : "f ∈ 1‥n → D"
  axiom axm0_3 : "v ∈ D"

eventb_machine BinarySearch0 where
  sees SearchCtx
  variables p q r
  invariant inv0_1 : "p ∈ 1‥n + 1"
  invariant inv0_2 : "q ∈ 1‥n + 1"
  invariant inv0_3 : "r ∈ p‥q"
  event INITIALISATION where
    action act1 : "p, q, r ≔ 1, n, 1"
  event final where
    guard grd1 : "p = q"
  event progress where
    status convergent
    guard grd1 : "p < q"
    any x
    guard grd2 : "x ∈ p‥q"
    action act1 : "p, q ≔ x, x"

eventb_machine BinarySearch1 where
  refines BinarySearch0
  sees SearchCtx
  variables p q r
  invariant inv1_1 : "p ≤ q"
  invariant inv1_2 : "f(p) ≤ v ∧ v < f(q + 1)"
  variant variant1 : "q − p"
  event dec where
    refines progress
    status convergent
    any x
    guard grd1 : "p < q"
    guard grd2 : "v < f(x)"
    action act1 : "q ≔ x − 1"
  event inc where
    refines progress
    status convergent
    any x
    guard grd1 : "p < q"
    guard grd2 : "f(x) ≤ v"
    action act1 : "p ≔ x"

/-! Chapter 15.5--15.8: minimum, partition, sorting and reversal. -/

eventb_machine ArrayPrograms where
  sees SearchCtx
  variables a b i j k r
  invariant inv0_1 : "a ∈ 1‥n"
  invariant inv0_2 : "b ∈ 1‥n"
  invariant inv0_3 : "i ∈ 1‥n + 1 ∧ j ∈ 1‥n + 1"
  event INITIALISATION where
    action act1 : "a, b, i, j, k, r ≔ 1, n, 1, n, 0, 0"
  event minimum where
    guard grd1 : "i ≤ j"
    action act1 : "r ≔ min({x · x ∈ i‥j ∣ f(x)})"
  event partition where
    guard grd1 : "i < j"
    any x
    guard grd2 : "x ∈ i‥j"
    action act1 : "k ≔ x"
  event sort_left where
    guard grd1 : "i < j"
    action act1 : "i ≔ i + 1"
  event sort_right where
    guard grd1 : "i < j"
    action act1 : "j ≔ j − 1"
  event reverse_progress where
    status convergent
    guard grd1 : "i < j"
    action act1 : "i, j ≔ i + 1, j − 1"

/-! Chapter 15.9: reversing a linked list. -/

eventb_context ListCtx where
  sets S
  constants d f l c nil
  axiom axm0_1 : "d ⊆ S"
  axiom axm0_2 : "f ∈ d"
  axiom axm0_3 : "l ∈ d"
  axiom axm0_4 : "c ∈ d ∖ {l} ⇸ d ∖ {f}"
  axiom axm0_5 : "nil ∉ d"

eventb_machine ListReverse0 where
  sees ListCtx
  variables r
  invariant inv0_1 : "r ∈ S ↔ S"
  event INITIALISATION where
    action act1 : "r ≔ ∅"
  event reverse where
    action act1 : "r ≔ c∼"

eventb_machine ListReverse1 where
  refines ListReverse0
  sees ListCtx
  variables r a b p
  invariant inv1_1 : "p ∈ d"
  invariant inv1_2 : "a ∈ S ↔ S"
  invariant inv1_3 : "b ∈ S ↔ S"
  invariant inv1_4 : "c = a ∪ b"
  event INITIALISATION where
    action act1 : "r, a, b, p ≔ ∅, ∅, c, f"
  event reverse where
    refines reverse
    guard grd1 : "b = ∅"
    action act1 : "r ≔ a"
  event progress where
    status convergent
    guard grd1 : "p ∈ dom(b)"
    action act1 : "p ≔ b(p)"
    action act2 : "a(b(p)) ≔ p"
    action act3 : "b ≔ {p} ◁ b"

/-! Chapter 15.10: square root by defect, including two refinements. -/

eventb_context RootCtx where
  constants n f
  axiom axm0_1 : "n ∈ ℕ"

eventb_machine SquareRoot0 where
  sees RootCtx
  variables r
  invariant inv0_1 : "r ∈ ℕ"
  variant variant1 : "n − r"
  event INITIALISATION where
    action act1 : "r ≔ 0"
  event final where
    guard grd1 : "r ^ 2 ≤ n ∧ n < (r + 1) ^ 2"
  event progress where
    status anticipated
    guard grd1 : "(r + 1) ^ 2 ≤ n"
    action act1 : "r ≔ r + 1"

eventb_machine SquareRoot1 where
  refines SquareRoot0
  sees RootCtx
  variables r a b
  invariant inv1_1 : "a = (r + 1) ^ 2"
  invariant inv1_2 : "b = 2 ∗ r + 3"
  event INITIALISATION where
    action act1 : "r, a, b ≔ 0, 1, 3"
  event progress where
    refines progress
    status convergent
    guard grd1 : "a ≤ n"
    action act1 : "r, a, b ≔ r + 1, a + b, b + 2"

/-! Chapter 15.11: inverse of an increasing function. -/

eventb_machine Inverse0 where
  sees RootCtx
  variables r
  invariant inv0_1 : "r ∈ ℕ"
  invariant inv0_2 : "∀i,j · i ∈ ℕ ∧ j ∈ ℕ ∧ i < j ⇒ f(i) < f(j)"
  event INITIALISATION where
    action act1 : "r ≔ 0"
  event final where
    guard grd1 : "f(r) ≤ n ∧ n < f(r + 1)"
  event progress where
    status anticipated
    guard grd1 : "n < f(r + 1)"
    action act1 : "r ≔ r + 1"

eventb_machine Inverse1 where
  refines Inverse0
  sees RootCtx
  variables r p q
  invariant inv1_1 : "r ≤ q"
  invariant inv1_2 : "f(r) ≤ n ∧ n < f(q + 1)"
  variant variant1 : "q − r"
  event INITIALISATION where
    action act1 : "r, q ≔ 0, n"
  event dec where
    refines progress
    status convergent
    guard grd1 : "r < q"
    guard grd2 : "n < f((r + 1 + q) ÷ 2)"
    action act1 : "q ≔ (r + 1 + q) ÷ 2 − 1"
  event inc where
    refines progress
    status convergent
    guard grd1 : "r < q"
    guard grd2 : "f((r + 1 + q) ÷ 2) ≤ n"
    action act1 : "r ≔ (r + 1 + q) ÷ 2"

def programsProject : Typing.Project :=
  [ { name := "NotationCtx", elem := NotationCtx }
  , { name := "NotationMachine", elem := NotationMachine }
  , { name := "MathCtx", elem := MathCtx }
  , { name := "MathMachine", elem := MathMachine }
  , { name := "SimpleProgram", elem := SimpleProgram }
  , { name := "SearchCtx", elem := SearchCtx }
  , { name := "BinarySearch0", elem := BinarySearch0 }
  , { name := "BinarySearch1", elem := BinarySearch1 }
  , { name := "ArrayPrograms", elem := ArrayPrograms }
  , { name := "ListCtx", elem := ListCtx }
  , { name := "ListReverse0", elem := ListReverse0 }
  , { name := "ListReverse1", elem := ListReverse1 }
  , { name := "RootCtx", elem := RootCtx }
  , { name := "SquareRoot0", elem := SquareRoot0 }
  , { name := "SquareRoot1", elem := SquareRoot1 }
  , { name := "Inverse0", elem := Inverse0 }
  , { name := "Inverse1", elem := Inverse1 } ]

private def hasPO (machine name : String) : Bool :=
  (POG.generate programsProject machine).any (·.name == name)

#guard hasPO "NotationMachine" "INITIALISATION/inv0_1/INV"
#guard hasPO "MathMachine" "INITIALISATION/inv0_1/INV"
#guard hasPO "BinarySearch1" "inv1_2/WD"
#guard hasPO "ArrayPrograms" "INITIALISATION/inv0_1/INV"
#guard hasPO "ListReverse1" "INITIALISATION/inv1_1/INV"
#guard hasPO "SquareRoot1" "INITIALISATION/inv1_1/INV"
#guard hasPO "Inverse1" "INITIALISATION/inv1_1/INV"

/-! Witness coverage regression: the openETCS-style refinement shape has both a
feasibility statement and the hypothesis-only well-definedness record. -/
def witnessObligations := POG.generate programsProject "NotationMachine"

#guard witnessObligations.map (·.name) |>.contains "witness_example/wit1/WFIS"
#guard witnessObligations.map (·.name) |>.contains "witness_example/wit1/WWD"
#guard (witnessObligations.find? (·.name == "witness_example/wit1/WFIS")).bind (·.goal) |>.isSome
#guard (witnessObligations.find? (·.name == "witness_example/wit1/WWD")).bind (·.goal) |>.isNone
#guard (witnessObligations.find? (·.name == "witness_example/wit1/WFIS")).bind
    (fun obligation => obligation.goal.map Formula.print) ==
  some "(∃ (v ⦂ D) · (v = f(i)))"
#guard (witnessObligations.find? (·.name == "witness_example/wit1/WFIS")).map
    (fun obligation => obligation.hyps.map Formula.print) == some
  ["(0 < n)", "(f ∈ ((1 ‥ n) → D))", "(∀ x · ((x ∈ (1 ‥ n)) ⇒ (x ∈ ℕ)))",
   "(x ∈ ℕ)", "(y ∈ ℕ)", "(g ∈ ((1 ‥ n) ⇸ D))", "(v ∈ D)"]
#guard !(witnessObligations.find? (·.name == "witness_example/wit1/WFIS")).bind
    (fun obligation => obligation.goal.map Formula.print) ==
  some "(∃ (v ⦂ D) · (v = f(i) ∧ FALSE))"
