# Native Event-B development environment

The native Lean/Event-B environment is the source of truth. Rodin artifacts are
compatibility input/output only; no runtime Rodin dependency is allowed.

## Active roadmap

The design and dependencies are documented in
[`notes/architecture.md`](notes/architecture.md). These four checkboxes are the
canonical milestones; the sections below contain their implementation tasks.

The first four roadmap milestones and the P4 integration boundary have an implemented,
tested result. Local corpus evidence remains explicitly external-trusted, never kernel
proof.

## Prototype v1 contract

Prototype v1 is complete when every item below is checked. It is a reference checker and
trust ledger, not a general-purpose automatic Event-B prover.

- [x] Read and analyze the pinned Rodin corpus losslessly through P3b.
- [x] Author native models and theories with scoped diagnostics and source ranges.
- [x] Read Rossi `.eventb` and Rodin `.tuf` inputs through the shared pipeline.
- [x] Present models, obligations, and trust evidence in CLI and ProofWidgets.
- [x] Run the local corpus baseline on all P3-matched obligations.
- [x] Replay kernel evidence and reject stale, forged, or mislabelled evidence.
- [x] Build every executable example and document the reproducible verification contract.
- [x] Leave all deliberate unsupported ceilings explicit in diagnostics and notes.

## P4 integration plan (complete)

- [x] Run the deterministic local prover over the 1133 P3-matched canonical obligations.
- [x] Accept results only through `Trust.Ledger.attach` and retain fingerprints.
- [x] Report external, kernel, and unproved counts in generated `STATUS.md`.
- [x] Add stale/forged evidence regression checks at the integrated boundary.
- [x] Keep P0–P3b ratchets unchanged and compare P4 with the Rodin `.bps` bar.

The existing milestones below and this integration plan are complete; no milestone is
open. Expanding the local prover is future capacity work, not an untracked issue.

## Completed execution checklist

- [x] Recover the multi-level refinement obligations: P3 now matches all 1133 Rodin
  obligation names.
- [x] Add differential P3b gates for WD, GRD, SIM, and ordered hypotheses. The gate
  compares all 1124 derived `.bpo` sequents; 394 generated goals without a Rodin
  sequent remain explicit coverage data.
- [x] Make resolved theory symbols, definitions, constructors, and rewrite rules flow
  through scoped typing, translation, POG normalization, and proof input.
- [x] Add project dependency loading, theory validation commands, and LSP regression
  fixtures.
- [x] Add a reproducible local prover/discharge baseline with audited external evidence.

- [x] R1: translate the supported Event-B formula language into kernel-checked Lean terms.
- [x] R2: validate and embed datatypes, definitions, rewrite rules, inference rules,
  and theorems.
- [x] R3: attach replayable prover evidence with explicit trust modes.
- [x] R4: add optional Rodin theory and proof-status I/O without a Rodin runtime
  dependency.

## Core language and environment

- [x] Define the core Event-B prelude (`BOOL`, `TRUE`, `FALSE`, `ℤ`, `ℕ`, and
  core operators) in one registry.
- [x] Define `Theory.Env` for the prelude and imported theories.
- [x] Connect `Theory.Env` to component model scopes.
- [x] Give every symbol a stable identity, type, documentation, and source range.
- [x] Specify conflict and shadowing rules against Event-B visibility semantics.

## Rossi `.eventb` input

Rossi remains the modern text/LSP authoring workflow. `eventb-lean` reads that format
as an independent Lean reference implementation: it lowers text into the shared model,
then runs the existing scope checker, POG, and trust ledger. The [Event-B Mathematical
Language specification][kernel-lang] is the formula-language parity target.

- [x] Read one or more Rossi contexts/machines from a `.eventb` file.
- [x] Load Rossi files and mixed Rossi/Rodin source directories in the CLI.
- [x] Preserve labels, theorem flags, statuses, witnesses, refinements, variants, and
  enumerated-set metadata.
- [x] Exercise compact, multiline, commented, and published Rossi examples.
- [x] Add token-aware formula/action boundary handling for wrapped formulas and adjacent
  unlabelled actions.
- [x] Pin a differential fixture matrix against the Rossi parser and the kernel-language
  lexical/precedence rules.

[kernel-lang]: https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/11/4/kernel_lang.pdf

## R2. Datatypes and theory rules

- [x] Add native Lean syntax for basic theory declarations and imports.
- [x] Type-check imported unary expression declarations against model formulas.
- [x] Type-check imported predicates represented as relations into `BOOL`.
- [x] Support operators, predicates, datatypes, and axiomatic definitions.
- [x] Support typing and well-definedness rules.
- [x] Support rewrite rules, inference rules, and theorems.
- [x] Support polymorphic theorem instantiation and type-variable declarations.
- [x] Validate theory soundness with generated proof obligations.

## Theory-aware toolchain

- [x] Make lexing, parsing, AST resolution, typing, WD, and pretty-printing
  theory-aware at their respective boundaries; unresolved constructs remain diagnostics.
- [x] Make scoped POG typing and WD classification consume theory metadata.
- [x] Make POG and prover backends consume resolved theory output: POG normalizes
  checked rules and the prover receives canonical obligations.
- [x] Preserve unsupported constructs as explicit diagnostics, never silently
  treating them as ordinary identifiers.

## R1. Full formula translation and Lean embedding

- [x] Map resolved Event-B types, sets, products, and theory carriers to Lean types.
- [x] Embed resolved Event-B types, expressions, predicates, and theories in Lean.
- [x] Translate definitions and datatype denotations to kernel-checked Lean terms.
- [x] Represent axiomatic assumptions without hiding them as trusted theorems.
- [x] Translate binders, primed variables, partial operators, and well-definedness
  hooks.
- [x] Expose translated POG goals and hypotheses to the semantic proof layer.
- [x] Reject unsupported or unresolved terms with actionable diagnostics.
- [x] Provide a typed trust ledger that defaults generated obligations to `unproved`.
- [x] Record kernel, SMT, Rodin-imported, and external trust in the ledger.

## R3. Prover evidence

- [x] Define a canonical obligation statement and stable fingerprint.
- [x] Replay Lean proof terms before assigning the `kernel` trust mode.
- [x] Record solver, version, input digest, and verifier for external evidence.
- [x] Import Rodin results only as `rodinImported`, never as kernel proofs.
- [x] Reject stale, missing, forged, or mislabelled evidence.
- [x] Show per-obligation evidence and trust in the CLI and ProofWidgets.
- [x] Compare discharge results with `.bps` without weakening the earlier gates.

## Native UX and project tooling

- [x] Add project/theory dependency loading and validation commands.
- [x] Add a native scoped POG command for an explicit theory environment.
- [x] Add source ranges for native theory symbols for hover/Go-to-Definition.
- [x] Add native-theory and initial trust summaries to ProofWidgets.
- [x] Render scoped native-theory obligations through an explicit widget command.
- [x] Add source locations and per-obligation trust evidence to ProofWidgets.
- [x] Add a native example covering an imported theory symbol.
- [x] Add native examples covering a Boolean theory and an imported operator.

## R4. Optional Rodin theory I/O and verification

- [x] Keep the existing Rodin corpus reader and gates green throughout.
- [x] Add optional Rodin theory import/export after native theories work.
- [x] Validate imported theory dependencies through `Theory.add` and scoped lookup.
- [x] Round-trip supported declarations without changing their resolved meaning.
- [x] Report unsupported constructs with declaration paths and actionable diagnostics.
- [x] Add negative tests for scope, conflicts, typing, WD, and theory visibility.
- [x] Add LSP tests for user symbols, prelude identifiers, and theory definitions.
- [x] Run `lake build`, `lake exe gates`, and `scripts/style-check.py` before every
  commit.

## Commit invariant

Each implementation commit updates the relevant R1–R4 task and leaves the build,
corpus gates, and style checks green. Unsupported constructs remain explicit data and
diagnostics; they never become `sorry`, an implicit axiom, or an unrelated identifier.

No unchecked milestone remains. Deliberate ceilings are documented in the code and
diagnostics: multi-parameter definition embedding needs an explicit semantic binding,
and rewrite matching does not guess through binders or set-builder bodies.
