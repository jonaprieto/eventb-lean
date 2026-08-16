/- Exact guard-source extraction checks. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def guardedProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.variable [("org.eventb.core.identifier", "x")] []
        , .invariant [("org.eventb.core.label", "type"),
                      ("org.eventb.core.predicate", "x ∈ ℤ")] []
        , .event [("org.eventb.core.label", "INITIALISATION")] []
        , .event [("org.eventb.core.label", "step")]
          [.guard [("org.eventb.core.label", "g"),
                   ("org.eventb.core.predicate", "x ∈ ℤ")] []]] }]

private def malformedGuardProject : EventB.Typing.Project :=
  [{ name := "M"
     elem := .machineFile [("org.eventb.core.name", "M")]
       [.event [("org.eventb.core.label", "step")]
          [.guard [("org.eventb.core.label", "g")] []]] }]

#guard eventGuardPredicates guardedProject "M" "step" ==
  some [.bin "∈" (.id "x") (.id "ℤ")]
#guard (CheckedGuardSource.fromProject Theory.empty guardedProject "M" "step").isSome
#guard eventGuardPredicates guardedProject "M" "missing" == none
#guard eventGuardPredicates malformedGuardProject "M" "step" == none
#guard (CheckedGuardSource.fromProject Theory.empty malformedGuardProject "M" "step").isNone

end EventB.POG
