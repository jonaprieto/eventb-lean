/- Exact provenance checks for merged-event source binding. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def mergeFixtureProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [ .variable [("org.eventb.core.identifier", "x")] []
       , .invariant [("org.eventb.core.label", "inv"),
                    ("org.eventb.core.predicate", "x ∈ ℤ")] []
       , .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "left")]
           [ .guard [("org.eventb.core.label", "g0"),
                     ("org.eventb.core.predicate", "x = 0")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ x")] [] ]
       , .event [("org.eventb.core.label", "right")]
           [ .guard [("org.eventb.core.label", "g1"),
                     ("org.eventb.core.predicate", "x = 1")] []
           , .action [("org.eventb.core.label", "set"),
                      ("org.eventb.core.assignment", "x ≔ x")] [] ] ] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [ .refinesMachine [("org.eventb.core.target", "A")] []
         , .variable [("org.eventb.core.identifier", "x")] []
         , .event [("org.eventb.core.label", "INITIALISATION")] []
         , .event [("org.eventb.core.label", "merge")]
             [ .refinesEvent [("org.eventb.core.target", "left")] []
             , .refinesEvent [("org.eventb.core.target", "right")] []
             , .guard [("org.eventb.core.label", "g"),
                       ("org.eventb.core.predicate", "x = 0 ∨ x = 1")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ x")] [] ] ] }]

#guard EventB.POG.eventRefinementTargets mergeFixtureProject "B" "merge" ==
  ["left", "right"]
#guard EventB.POG.eventRefinementTargetLocators mergeFixtureProject "B" "merge" ==
  [("A", "left"), ("A", "right")]
#guard (CheckedMergeSource.fromProject EventB.Theory.empty mergeFixtureProject "B" "merge").isSome
#guard (CheckedMergeSource.fromProject EventB.Theory.empty mergeFixtureProject "B" "left").isNone
#guard (CheckedMergeSource.fromProject EventB.Theory.empty mergeFixtureProject "B" "missing").isNone

private def rawMergeObligation : Obligation :=
  { component := "B"
    name := "merge/MRG"
    kind := "MRG"
    goal := some (.id "source") }

#guard rawMergeObligation.sourceBound mergeFixtureProject
#guard !( { rawMergeObligation with name := "left/MRG" }.sourceBound mergeFixtureProject )

end EventB.POG
