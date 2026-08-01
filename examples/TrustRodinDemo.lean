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

#guard match Trust.Rodin.importStatuses source with
  | .ok [status] =>
      let result := Trust.Rodin.compare [obligation] [status]
      result.discharged == 1 && result.automatic == 1
  | _ => false

#guard match Trust.Rodin.importStatuses source with
  | .ok [status] => match Trust.Rodin.attach
      (Trust.Ledger.ofObligations [obligation]) obligation "demo.bps" status with
    | .ok ledger => ledger.count .rodinImported == 1
    | .error _ => false
  | _ => false

end EventB.TrustRodinDemo
