/- Rodin proof status is imported as explicit trust, never as a kernel proof. -/
import EventB.Trust.Rodin

namespace EventB.TrustRodinDemo

open EventB

private def obligation : POG.Obligation :=
  { component := "Demo", name := "evt/inv/INV", kind := "INV", goal := some (.id "⊤") }

private def source :=
  "<?xml version=\"1.0\"?><org.eventb.core.psFile><org.eventb.core.psStatus " ++
    "name=\"evt/inv/INV\" " ++
    "org.eventb.core.confidence=\"1000\" org.eventb.core.psManual=\"false\"/>" ++
    "</org.eventb.core.psFile>"

private def provenance : Trust.Rodin.Provenance :=
  { model := "<?xml version=\"1.0\"?><org.eventb.core.machineFile " ++
      "org.eventb.core.name=\"Demo\"/>"
    bpo := "<?xml version=\"1.0\"?>" ++
      "<org.eventb.core.poFile source=\"Demo.bum\"><org.eventb.core.poSequent " ++
      "name=\"evt/inv/INV\"><org.eventb.core.poPredicate " ++
      "org.eventb.core.predicate=\"⊤\"/></org.eventb.core.poSequent></org.eventb.core.poFile>"
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
