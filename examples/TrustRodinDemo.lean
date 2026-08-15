/- Rodin proof status is imported as explicit trust, never as a kernel proof. -/
import EventB.Trust.Rodin

namespace EventB.TrustRodinDemo

open EventB

private def obligation : POG.Obligation :=
  { component := "Demo", name := "INITIALISATION/inv/INV", kind := "INV"
    goal := some (.bin "∈" (.num 0) (.id "ℤ")) }

private def source :=
  "<?xml version=\"1.0\"?><org.eventb.core.psFile><org.eventb.core.psStatus " ++
    "name=\"INITIALISATION/inv/INV\" " ++
    "org.eventb.core.confidence=\"1000\" org.eventb.core.psManual=\"false\"/>" ++
    "</org.eventb.core.psFile>"

private def provenance : Trust.Rodin.Provenance :=
  { models := [{ component := "Demo", kind := .machine, bytes :=
    ("<?xml version=\"1.0\"?><org.eventb.core.machineFile " ++
      "org.eventb.core.name=\"Demo\"><org.eventb.core.variable " ++
      "org.eventb.core.identifier=\"x\"/><org.eventb.core.invariant " ++
      "org.eventb.core.label=\"inv\" org.eventb.core.predicate=\"x ∈ ℤ\"/>" ++
      "<org.eventb.core.event org.eventb.core.label=\"INITIALISATION\"><org.eventb.core.action " ++
      "org.eventb.core.label=\"set\" org.eventb.core.assignment=\"x ≔ 0\"/>" ++
      "</org.eventb.core.event></org.eventb.core.machineFile>").toUTF8 }]
    bpo := "<?xml version=\"1.0\"?>" ++
      "<org.eventb.core.poFile source=\"Demo.bum\"><org.eventb.core.poSequent " ++
      "name=\"INITIALISATION/inv/INV\"><org.eventb.core.poPredicate " ++
      "org.eventb.core.predicate=\"(0 ∈ ℤ)\"/></org.eventb.core.poSequent></org.eventb.core.poFile>"
    statuses := source }

#guard match Trust.Rodin.importStatuses source with
  | .ok [status] =>
      let result := Trust.Rodin.compare [obligation] [status]
      result.discharged == 1 && result.automatic == 1
  | _ => false

#guard match Trust.Rodin.importStatuses source with
  | .ok [status] => match Trust.Rodin.attachProvenance
      (Trust.Ledger.ofObligations [obligation]) obligation provenance status with
    | .ok ledger => ledger.count .rodinImported == 1
    | .error _ => false
  | _ => false

end EventB.TrustRodinDemo
