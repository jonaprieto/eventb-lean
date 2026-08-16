/- Typed finite-set evaluator fixtures for ℙ(T), finite, and subset goals. -/

import EventB.POGSoundness

namespace EventB.POG

private def setEnv : ValueEnv :=
  { values := [("S", .set [.integer 0, .integer 1])] }

private def badSetEnv : ValueEnv :=
  { values := [("S", .set [.integer 0, .boolean true])] }

private def integerUniverseEnv : ValueEnv :=
  { values := [("S", .integerSet)] }

private def setTransition : CheckedBeforeAfter :=
  { before := setEnv
    after := { values := [("S", .set [.integer 1])] }
    declarations := [("S", .pow .int)] }

#guard (EventB.Formula.parse "S ∈ ℙ(ℤ)").toOption ==
  some (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ")))
#guard ValueEnv.validationOk 128 [("S", .pow .int)] setEnv
#guard !ValueEnv.validationOk 128 [("S", .pow .int)] badSetEnv

#guard evalPredicateAtFuel 128 setEnv
    (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))) == .ok true
#guard evalPredicateAtFuel 128 setEnv
    (.app (.id "finite") (.id "S")) == .ok true
#guard ValueEnv.validationOk 128 [("S", .pow .int)] integerUniverseEnv
#guard evalPredicateAtFuel 128 integerUniverseEnv
    (.app (.id "finite") (.id "S")) == .ok false
#guard evalBeforeAfter 128 setTransition
    (.bin "⊂" (.id "S'") (.id "S")) == .ok true
#guard match evalPredicateAtFuel 128 badSetEnv
    (.bin "∈" (.id "S") (.pre "ℙ" (.id "ℤ"))) with
  | .error _ => true
  | .ok _ => false

private def witnessBody : EventB.Formula.Term :=
  .bin "=" (.id "p") (.num 0)

#guard evalPredicateOverFiniteDomain 128 {} "p"
    [.integer 0, .integer 1] witnessBody == .ok true
#guard evalPredicateOverFiniteDomain 128 {} "p"
    [.integer 1, .integer 2] witnessBody == .ok false

example : ∃ candidate, candidate ∈ ([.integer 0, .integer 1] : List Value) ∧
    evalPredicateAtFuel 128 (({} : ValueEnv).set "p" candidate) witnessBody = .ok true := by
  apply evalPredicateOverFiniteDomain_true 128 {} "p"
    [.integer 0, .integer 1] witnessBody
  native_decide

end EventB.POG
