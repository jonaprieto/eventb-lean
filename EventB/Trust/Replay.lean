/-
Replayable validation for trust-ledger evidence.

Kernel evidence names a Lean declaration. This module resolves that declaration,
translates the POG sequent, and asks the kernel's elaborator whether the proof
type is definitionally equal to the translated statement. Other evidence remains
explicitly trusted metadata; it is never reported as kernel replay.
-/

import EventB.Trust
import EventB.Trust.Rodin
import EventB.Formula.Translate

namespace EventB.Trust.Replay

open Lean Elab Command Meta
open EventB EventB.Embedding EventB.Formula EventB.POG

structure Report where
  mode : Mode
  replayed : Bool := false
  declaration : String := ""
  fingerprint : String := ""
  axioms : List String := []
  deriving BEq, Repr, Inhabited

private def mkImplications : List Expr → Expr → MetaM Expr
  | [], conclusion => pure conclusion
  | premise :: premises, conclusion => do
      let rest ← mkImplications premises conclusion
      mkArrow premise rest

private def statement (context : Embedding.KernelContext)
    (obligation : POG.Obligation) : MetaM Expr := do
  let goal ← match obligation.goal with
    | some goal => Embedding.translatePredicate context goal
    | none => throwError s!"obligation `{obligation.name}` has no translated goal"
  let hypotheses ← obligation.hyps.mapM (Embedding.translatePredicate context)
  mkImplications hypotheses goal

/-- Translate a complete obligation sequent without assigning trust evidence. -/
def translateStatement (context : Embedding.KernelContext)
    (obligation : POG.Obligation) : MetaM Expr :=
  statement context obligation

private def declarationName (declaration : String) : Name := declaration.toName

def proofFingerprint (context : Embedding.KernelContext) (obligation : POG.Obligation) : String :=
  Trust.fingerprint (obligation.canonical ++
    "\nsemantic-context=" ++ context.semanticFingerprint)

private def proofTerm (declaration : String) : MetaM Expr := do
  let name := declarationName declaration
  let info ← getConstInfo name
  if info.isUnsafe then
    throwError s!"proof declaration `{declaration}` is unsafe"
  let proof ← mkConstWithLevelParams name
  let type ← inferType proof
  unless ← isDefEq type info.type do
    throwError s!"proof declaration `{declaration}` has an inconsistent type"
  pure proof

private def specializeProof (proof : Expr) : List KernelBinding → MetaM Expr
  | [] => pure proof
  | binding :: bindings => do
      let proofType ← whnf (← inferType proof)
      match proofType with
      | .forallE _ expected _ _ =>
          let actual ← inferType binding.value
          unless ← isDefEq actual expected do
            throwError s!"proof `{binding.name}` has type {actual}, expected {expected}"
          specializeProof (mkApp proof binding.value) bindings
      | _ =>
          throwError s!"proof declaration has no parameter for `{binding.name}`"

private def declarationDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo value => value.value.getUsedConstants
  | .thmInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | _ => #[]

private def axiomNames (initial : List Name) : MetaM NameSet := do
  let mut pending := initial
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name then
      seen := seen.insert name
      let info ← getConstInfo name
      if info.isUnsafe then
        throwError s!"kernel evidence depends on unsafe declaration `{name}`"
      if info matches .axiomInfo _ then
        axioms := axioms.insert name
      pending := pending ++ (declarationDependencies info).toList
  pure axioms

private def sortedNames (names : NameSet) : List String :=
  names.toList.map (·.toString false) |>.mergeSort (· < ·)

private def actualAxioms (proof : Expr) : MetaM (List String) := do
  let names ← axiomNames proof.getUsedConstants.toList
  pure (sortedNames names)

private def expectedAxioms (evidence : Evidence) : MetaM (String × List String) := do
  match evidence with
  | .kernel declaration axioms =>
      pure (declaration, axioms.map fun name => (name.toName).toString false)
  | _ => throwError "kernel replay requires kernel evidence"

/-- Validate an in-memory proof term against the translated sequent. -/
def validateTerm (context : Embedding.KernelContext)
    (obligation : POG.Obligation) (proof : Expr)
    (declaration : String := "<term>")
    (declaredAxioms : List String := []) : MetaM Report := do
  unless obligation.diagnostics.isEmpty do
    throwError s!"obligation `{obligation.name}` has diagnostics"
  unless obligation.goal.isSome do
    throwError s!"obligation `{obligation.name}` has no translated goal"
  if proof.hasMVar then
    throwError s!"kernel proof `{declaration}` contains unresolved metavariables"
  let expected ← translateStatement context obligation
  let proofType ← inferType proof
  unless ← isDefEq proofType expected do
    throwError s!"proof term does not prove `{obligation.name}`"
  let actualAxioms ← actualAxioms proof
  unless !actualAxioms.contains "sorryAx" do
    throwError s!"kernel proof `{declaration}` depends on forbidden axiom `sorryAx`"
  let declared := declaredAxioms.map fun name => (name.toName).toString false
  unless actualAxioms == declared.mergeSort (· < ·) do
    throwError s!"axiom metadata mismatch for `{declaration}`: declared " ++
      s!"[{String.intercalate ", " declared}], found " ++
      s!"[{String.intercalate ", " actualAxioms}]"
  pure (Report.mk .kernel true declaration (proofFingerprint context obligation) actualAxioms)

private def replayKernel (context : Embedding.KernelContext)
    (obligation : POG.Obligation) (evidence : Evidence) : MetaM Report := do
  let (declaration, declaredAxioms) ← expectedAxioms evidence
  let proof ← proofTerm declaration
  let proof ← specializeProof proof context.bindings
  validateTerm context obligation proof declaration declaredAxioms

def validate (context : Embedding.KernelContext) (obligation : POG.Obligation) :
    Evidence → MetaM Report
  | evidence@(.kernel ..) => replayKernel context obligation evidence
  | .rodinImported .. =>
      throwError "legacy status-only Rodin evidence is not trusted; attach model and PO provenance"
  | evidence@(.rodinImportedProvenance model bpo statuses digest manual) => do
      let provenance : Rodin.Provenance := { model, bpo, statuses }
      unless digest == Rodin.provenanceDigest provenance do
        throwError "Rodin provenance digest mismatch"
      let parsed ← match Rodin.importStatuses statuses with
        | .ok parsed => pure parsed
        | .error error => throwError error.message
      match parsed.find? (fun status => status.name == obligation.name) with
      | none => throwError s!"Rodin evidence artifact has no status for `{obligation.name}`"
      | some status =>
          match Rodin.validateProvenance obligation provenance status with
          | .ok _ => pure ()
          | .error error => throwError error.message
          unless status.manual == manual do
            throwError s!"Rodin evidence manual flag mismatch for `{obligation.name}`"
      unless obligation.diagnostics.isEmpty do
        throwError s!"obligation `{obligation.name}` has diagnostics"
      unless obligation.goal.isSome do
        throwError s!"obligation `{obligation.name}` has no translated goal"
      pure { mode := evidence.mode, fingerprint := proofFingerprint context obligation }
  | evidence => do
      unless obligation.diagnostics.isEmpty do
        throwError s!"obligation `{obligation.name}` has diagnostics"
      unless obligation.goal.isSome do
        throwError s!"obligation `{obligation.name}` has no translated goal"
      unless evidence.isWellFormed do
        throwError "evidence metadata is incomplete"
      pure { mode := evidence.mode, fingerprint := proofFingerprint context obligation }

def validateEntry (context : Embedding.KernelContext) (obligation : POG.Obligation)
    (entry : Entry) : MetaM Report := do
  unless entry.component == obligation.component && entry.obligation == obligation.name do
    throwError s!"evidence entry does not identify `{obligation.component}:{obligation.name}`"
  unless entry.fingerprint == Trust.fingerprint obligation.canonical do
    throwError s!"evidence fingerprint mismatch for `{obligation.component}:{obligation.name}`"
  unless entry.canonical == obligation.canonical do
    throwError s!"evidence canonical mismatch for `{obligation.component}:{obligation.name}`"
  unless entry.mode == entry.evidence.mode do
    throwError s!"evidence mode mismatch for `{obligation.component}:{obligation.name}`"
  if entry.mode == .kernel then
    unless entry.semanticFingerprint == proofFingerprint context obligation do
      throwError s!"kernel evidence context mismatch for `{obligation.component}:{obligation.name}`"
  validate context obligation entry.evidence

#guard ({ mode := .kernel, replayed := true, declaration := "proof" } : Report).replayed
#guard ({ mode := .smt } : Report).mode == .smt
#guard Evidence.isWellFormed (.smt "z3" "4" "sha256:input" "checker")
#guard !Evidence.isWellFormed (.external "" "1" "digest" "checker")

namespace TestFixtures

theorem propextTrue : True := by
  have h : True = True := propext Iff.rfl
  exact Eq.mp h True.intro

def testInt : Int := 0

unsafe def unsafeTrue : True := True.intro

theorem reflexive (value : Int) : value = value := rfl

end TestFixtures

private def replayObligation : POG.Obligation :=
  { component := "Replay"
    name := "true/THM"
    kind := "THM"
    goal := some (.id "⊤") }

private meta def succeeds (action : TermElabM Report) : TermElabM Bool := do
  try
    let _ ← action
    pure true
  catch _ => pure false

private meta def checkReplay : TermElabM Unit := do
  let context : Embedding.KernelContext := {}
  let evidence := Evidence.kernel "True.intro" []
  unless ← succeeds (validate context replayObligation evidence) do
    throwError "valid kernel evidence did not replay"
  let specializedContext : Embedding.KernelContext :=
    { bindings := [{ name := "value", ty := .int, value := mkConst ``TestFixtures.testInt }] }
  let specializedObligation : POG.Obligation :=
    { component := "Replay", name := "value/reflexive/THM", kind := "THM"
      goal := some (.bin "=" (.id "value") (.id "value")) }
  unless ← succeeds (validate specializedContext specializedObligation
      (.kernel "EventB.Trust.Replay.TestFixtures.reflexive" [])) do
    throwError "universally quantified kernel evidence did not replay"
  let translated ← translateStatement specializedContext specializedObligation
  unless (← inferType translated).isSort do
    throwError "translated obligation sequent is not a proposition"
  unless !(← succeeds (validate context replayObligation
      (.kernel "True.intro" ["propext"]))) do
    throwError "forged axiom metadata was accepted"
  unless !(← succeeds (validate context
      { replayObligation with goal := some (.id "⊥") } evidence)) do
    throwError "stale proof evidence was accepted"
  unless !(← succeeds (validate context replayObligation
      (.kernel "EventB.Trust.Replay.missing" []))) do
    throwError "unresolved proof declaration was accepted"
  unless !(← succeeds (validate context replayObligation
      (.kernel "EventB.Trust.Replay.TestFixtures.unsafeTrue" []))) do
    throwError "unsafe proof declaration was accepted"
  let target ← translateStatement context replayObligation
  let openProof ← mkFreshExprMVar target
  unless !(← succeeds (validateTerm context replayObligation openProof)) do
    throwError "open metavariable proof was accepted"
  unless ← succeeds (validate context replayObligation
      (.kernel "EventB.Trust.Replay.TestFixtures.propextTrue" ["propext"])) do
    throwError "actual axiom metadata did not replay"
  let trusted := validate context replayObligation
    (.smt "z3" "4" "sha256:input" "checker")
  let report ← trusted
  unless report.mode == .smt && !report.replayed && !report.fingerprint.isEmpty do
    throwError "SMT evidence was reported as replayed"
  let external ← validate context replayObligation
    (.external "alt-ergo" "2" "sha256:po" "eventb-checker")
  unless external.mode == .external && !external.replayed do
    throwError "external evidence was reported as replayed"
  let rodinSource := "<?xml version=\"1.0\"?><org.eventb.core.psFile><org.eventb.core.psStatus " ++
    "name=\"true/THM\" org.eventb.core.confidence=\"1000\" " ++
    "org.eventb.core.psManual=\"true\"/></org.eventb.core.psFile>"
  unless !(← succeeds (validate context replayObligation
      (.rodinImported rodinSource (Trust.fingerprint rodinSource) true))) do
    throwError "legacy status-only Rodin evidence was accepted"
  unless !(← succeeds (validate context replayObligation
      (.rodinImported rodinSource (Trust.fingerprint rodinSource) false))) do
    throwError "Rodin manual flag mismatch was accepted"
  unless !(← succeeds (validate context replayObligation
      (.rodinImported rodinSource "forged" true))) do
    throwError "forged Rodin artifact digest was accepted"
  let entry : Entry :=
    { component := replayObligation.component
      obligation := replayObligation.name
      fingerprint := Trust.fingerprint replayObligation.canonical
      canonical := replayObligation.canonical
      semanticFingerprint := proofFingerprint context replayObligation
      mode := .kernel
      evidence := evidence }
  let entryReport ← validateEntry context replayObligation entry
  unless entryReport.replayed do
    throwError "valid ledger evidence did not replay"
  unless !(← succeeds (validateEntry
      { bindings := [{ name := "different", ty := .int, value := mkConst ``TestFixtures.testInt }] }
      replayObligation entry)) do
    throwError "kernel evidence accepted a different semantic context"
  unless !(← succeeds (validateEntry context
      { replayObligation with goal := some (.id "⊥") } entry)) do
    throwError "stale ledger evidence was accepted"
  unless !(← succeeds (validateEntry context replayObligation
      { entry with mode := .smt })) do
    throwError "mislabelled ledger evidence was accepted"
  unless !(← succeeds (validate context replayObligation
      (.external "" "1" "digest" "checker"))) do
    throwError "incomplete external metadata was accepted"
  unless !(← succeeds (validate context
      { replayObligation with goal := none }
      (.external "checker" "1" "digest" "verifier"))) do
    throwError "statement-less external evidence was accepted"
  unless !(← succeeds (validate context replayObligation
      (.rodinImported "" "digest" false))) do
    throwError "incomplete Rodin metadata was accepted"
  let valueZero := mkConst ``TestFixtures.testInt
  let valueOne := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
  let bindingObligation : POG.Obligation :=
    { component := "Replay", name := "bound/reflexive/THM", kind := "THM"
      goal := some (.bin "=" (.id "value") (.id "value")) }
  let reportZero ← validate
    { bindings := [{ name := "value", ty := .int, value := valueZero }] }
    bindingObligation (.kernel "EventB.Trust.Replay.TestFixtures.reflexive" [])
  let reportOne ← validate
    { bindings := [{ name := "value", ty := .int, value := valueOne }] }
    bindingObligation (.kernel "EventB.Trust.Replay.TestFixtures.reflexive" [])
  unless reportZero.fingerprint != reportOne.fingerprint do
    throwError "semantic binding changes did not change the proof fingerprint"

syntax (name := eventbReplayChecks) "#eventb_replay_checks" : command

@[command_elab eventbReplayChecks]
meta def elabReplayChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_replay_checks) => liftTermElabM do
      checkReplay
  | _ => throwUnsupportedSyntax

#eventb_replay_checks

end EventB.Trust.Replay
