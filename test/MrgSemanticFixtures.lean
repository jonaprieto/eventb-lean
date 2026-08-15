/- Source-bound merged-event semantics: labels and selected branch events stay paired. -/

import EventB.POG.RefinementAdapters

namespace EventB.POG

private def mergeSemanticProject : EventB.Typing.Project :=
  [{ name := "A"
     elem := .machineFile [("org.eventb.core.name", "A")]
       [ .event [("org.eventb.core.label", "INITIALISATION")] []
       , .event [("org.eventb.core.label", "left")] []
       , .event [("org.eventb.core.label", "right")] [] ] }
   , { name := "B"
       elem := .machineFile [("org.eventb.core.name", "B")]
         [ .refinesMachine [("org.eventb.core.target", "A")] []
         , .variable [("org.eventb.core.identifier", "x")] []
         , .event [("org.eventb.core.label", "INITIALISATION")] []
         , .event [("org.eventb.core.label", "merge")]
             [ .refinesEvent [("org.eventb.core.target", "left")] []
             , .refinesEvent [("org.eventb.core.target", "right")] []
             , .action [("org.eventb.core.label", "set"),
                        ("org.eventb.core.assignment", "x ≔ 0")] [] ] ] }]

private def mergeSource : CheckedMergeSource Theory.empty
    mergeSemanticProject "B" "merge" :=
  (CheckedMergeSource.fromProject Theory.empty mergeSemanticProject "B" "merge").get
    (by native_decide)

private def concreteEvent : Event Unit :=
  { grd := fun _ => True
    act := fun _ _ => True }

private def leftBranch : Event Bool :=
  { grd := fun state => state = false
    act := fun _ _ => True }

private def rightBranch : Event Bool :=
  { grd := fun state => state = true
    act := fun _ _ => True }

private def abstractMachine : Machine Bool :=
  { inv := fun _ => True
    init := fun _ => True
    events := [leftBranch, rightBranch] }

private def concreteMachine : Machine Unit :=
  { inv := fun _ => True
    init := fun _ => True
    events := [concreteEvent] }

private def splitContract : SplitSimulation concreteMachine abstractMachine
    (fun _ _ => True) :=
  { concreteEvent := concreteEvent
    concreteMember := by simp [concreteMachine]
    abstractEvents := [leftBranch, rightBranch]
    abstractNonempty := by simp
    abstractMember := by
      intro abstract member
      have branches : abstract = leftBranch ∨ abstract = rightBranch := by
        simpa using member
      rcases branches with rfl | rfl <;> simp [abstractMachine]
    guard := by
      intro _ abstract _ _
      cases abstract with
      | false => exact ⟨leftBranch, by simp, by simp [leftBranch]⟩
      | true => exact ⟨rightBranch, by simp, by simp [rightBranch]⟩
    action := by
      intro abstract _ _ _ member _ _ _ _
      have branches : abstract = leftBranch ∨ abstract = rightBranch := by
        simpa using member
      rcases branches with rfl | rfl <;>
        exact ⟨false, by simp [leftBranch, rightBranch], trivial⟩ }

private def sourceBranches : List (String × Event Bool) :=
  [("left", leftBranch), ("right", rightBranch)]

#guard mergeSource.targets == ["left", "right"]
#guard sourceBranches.map (·.1) == mergeSource.targets
#guard !([("wrong", leftBranch), ("right", rightBranch)].map (·.1) == mergeSource.targets)

example : [leftBranch, rightBranch] = sourceBranches.map (·.2) := by rfl

example : splitSimulationSemantic splitContract sourceBranches := by
  intro _ _ abstract _ _ _
  cases abstract with
  | false =>
      exact ⟨"left", leftBranch, false, by simp [sourceBranches],
        by simp [leftBranch], by simp [leftBranch], trivial⟩
  | true =>
      exact ⟨"right", rightBranch, true, by simp [sourceBranches],
        by simp [rightBranch], by simp [rightBranch], trivial⟩

private def foreignBranch : Event Bool :=
  { grd := fun _ => True
    act := fun _ _ => False }

example : ¬ splitSimulationSemantic splitContract
    [("foreign", foreignBranch)] := by
  intro semantic
  obtain ⟨label, branch, after, member, _, action, _⟩ :=
    semantic () () false trivial trivial trivial
  have pair : (label, branch) = ("foreign", foreignBranch) := by
    simpa using member
  cases pair
  simpa [foreignBranch] using action

/- A matching label is not enough: replacing the selected branch object must also
   invalidate the semantic contract.  This is the negative control for the adapter's
   still-explicit abstract-event provenance boundary. -/
example : ¬ splitSimulationSemantic splitContract
    [("left", foreignBranch), ("right", rightBranch)] := by
  intro semantic
  obtain ⟨label, branch, after, member, guard, action, _⟩ :=
    semantic () () false trivial trivial trivial
  have cases : (label, branch) = ("left", foreignBranch) ∨
      (label, branch) = ("right", rightBranch) := by
    simpa using member
  rcases cases with left | right
  · cases left
    simpa [foreignBranch] using action
  · cases right
    simpa [rightBranch] using guard

end EventB.POG
