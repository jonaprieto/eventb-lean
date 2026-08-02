/- A checked inventory of the deliberately small local discharge baseline. -/
import EventB.Prover.Local
import EventB.Prover.Kernel
import EventB.Trust.Replay

open EventB EventB.POG EventB.Prover.Local

private def obligations : List Obligation :=
  [{ component := "Demo", name := "true", kind := "THM", goal := some (.id "⊤") },
   { component := "Demo", name := "refl", kind := "THM",
     goal := some (.bin "=" (.id "x") (.id "x")) },
   { component := "Demo", name := "open", kind := "INV", goal := some (.id "x") }]

def baseline : List Result := obligations.map prove

#guard baseline.countP Result.discharged == 2
#guard baseline.countP (fun result => result.evidence.mode == .external) == 2

namespace KernelChecks

open Lean Elab Command Meta
open EventB EventB.Embedding EventB.Formula EventB.POG

private def trueObligation : Obligation :=
  { component := "Demo", name := "true", kind := "THM", goal := some (.id "⊤") }

private def exactObligation : Obligation :=
  { component := "Demo", name := "exact", kind := "THM",
    goal := some (.id "⊤"), hyps := [.id "⊤"] }

private def reflexiveObligation : Obligation :=
  { component := "Demo", name := "refl", kind := "THM"
    goal := some (.bin "=" (.num 1) (.num 1)) }

private def contradictionObligation : Obligation :=
  { component := "Demo", name := "contra", kind := "THM",
    goal := some (.bin "=" (.num 1) (.num 2)), hyps := [.id "⊥"] }

private def examples : List (EventB.Prover.Kernel.Rule × Obligation) :=
  [(.true, trueObligation), (.exactHypothesis, exactObligation),
   (.reflexive, reflexiveObligation), (.contradiction, contradictionObligation)]

private meta def succeeds (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    pure true
  catch _ => pure false

private meta def check : TermElabM Unit := do
  for (expected, obligation) in examples do
    let result ← EventB.Prover.Kernel.validate {} obligation
    unless result.discharged && result.rule == some expected do
      throwError s!"kernel rule did not discharge `{obligation.name}`"
  let rejected : Obligation :=
    { component := "Demo", name := "open", kind := "THM",
      goal := some (.bin "=" (.num 1) (.num 2)) }
  let openResult ← EventB.Prover.Kernel.prove {} rejected
  unless !openResult.discharged do
    throwError "kernel prover discharged an unsupported goal"
  let stale : Obligation := { examples.head!.2 with goal := some (.id "⊥") }
  unless !(← succeeds do
      let _ ← Trust.Replay.validateTerm {} stale (mkConst ``True.intro)) do
    throwError "kernel replay accepted a stale proof term"

syntax (name := eventbKernelChecks) "#eventb_kernel_checks" : command

@[command_elab eventbKernelChecks]
meta def elabKernelChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_kernel_checks) => liftTermElabM check
  | _ => throwUnsupportedSyntax

#eventb_kernel_checks

end KernelChecks
