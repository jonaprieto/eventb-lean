# Native Event-B development environment

The native Lean/Event-B environment is the source of truth. Rodin artifacts are
compatibility input/output only; no runtime Rodin dependency is allowed.

## Active roadmap

The design and dependencies are documented in
[`notes/architecture.md`](notes/architecture.md). These four checkboxes are the
canonical milestones; the sections below contain their implementation tasks.

- [ ] R1: complete full formula translation into kernel-checkable Lean terms.
- [ ] R2: add datatypes, definitions, rewrite rules, inference rules, and theorems.
- [ ] R3: attach replayable prover evidence with explicit trust modes.
- [ ] R4: add optional Rodin theory import/export without a Rodin runtime dependency.

## Core language and environment

- [x] Define the core Event-B prelude (`BOOL`, `TRUE`, `FALSE`, `ℤ`, `ℕ`, and
  core operators) in one registry.
- [x] Define `Theory.Env` for the prelude and imported theories.
- [x] Connect `Theory.Env` to component model scopes.
- [ ] Give every symbol a stable identity, type, documentation, and source range.
- [x] Specify conflict and shadowing rules against Event-B visibility semantics.

## R2. Datatypes and theory rules

- [x] Add native Lean syntax for basic theory declarations and imports.
- [x] Type-check imported unary expression declarations against model formulas.
- [x] Type-check imported predicates represented as relations into `BOOL`.
- [ ] Support operators, predicates, datatypes, and axiomatic definitions.
- [ ] Support typing and well-definedness rules.
- [ ] Support rewrite rules, inference rules, and polymorphic theorems.
- [ ] Validate theory soundness with generated proof obligations.

## Theory-aware toolchain

- [ ] Make lexing, parsing, AST resolution, typing, WD, and pretty-printing
  theory-aware.
- [x] Make scoped POG typing and WD classification consume theory metadata.
- [ ] Make POG and prover backends consume resolved theory declarations.
- [ ] Preserve unsupported constructs as explicit diagnostics, never silently
  treating them as ordinary identifiers.

## R1. Full formula translation and Lean embedding

- [x] Map resolved Event-B types, sets, products, and theory carriers to Lean types.
- [ ] Embed resolved Event-B types, expressions, predicates, and theories in Lean.
- [ ] Translate definitions and datatypes to kernel-checkable Lean declarations.
- [ ] Represent axiomatic assumptions without hiding them as trusted theorems.
- [ ] Translate binders, primed variables, partial operators, and well-definedness.
- [ ] Expose translated POG goals and hypotheses to the semantic proof layer.
- [ ] Reject unsupported or unresolved terms with source-located diagnostics.
- [x] Provide a typed trust ledger that defaults generated obligations to `unproved`.
- [ ] Record kernel, SMT, Rodin-imported, and external trust in the ledger.

## R3. Prover evidence

- [ ] Define a canonical obligation statement and stable fingerprint.
- [ ] Replay Lean proof terms before assigning the `kernel` trust mode.
- [ ] Record solver, version, input digest, and verifier for external evidence.
- [ ] Import Rodin results only as `rodinImported`, never as kernel proofs.
- [ ] Reject stale, missing, forged, or mislabelled evidence.
- [ ] Show per-obligation evidence and trust in the CLI and ProofWidgets.
- [ ] Compare discharge results with `.bps` without weakening the earlier gates.

## Native UX and project tooling

- [ ] Add project/theory dependency loading and validation commands.
- [x] Add a native scoped POG command for an explicit theory environment.
- [x] Add source ranges for native theory symbols for hover/Go-to-Definition.
- [x] Add native-theory and initial trust summaries to ProofWidgets.
- [x] Render scoped native-theory obligations through an explicit widget command.
- [ ] Add source locations and per-obligation trust evidence to ProofWidgets.
- [x] Add a native example covering an imported theory symbol.
- [x] Add native examples covering a Boolean theory and an imported operator.

## R4. Optional Rodin theory I/O and verification

- [ ] Keep the existing Rodin corpus reader and gates green throughout.
- [ ] Add optional Rodin theory import/export after native theories work.
- [ ] Validate imported theory dependencies through `Theory.add` and scoped lookup.
- [ ] Round-trip supported declarations without changing their resolved meaning.
- [ ] Report unsupported constructs with source locations and actionable diagnostics.
- [ ] Add negative tests for scope, conflicts, typing, WD, and theory visibility.
- [ ] Add LSP tests for user, prelude, and theory definitions.
- [ ] Run `lake build`, `lake exe gates`, and `scripts/style-check.py` before
  every commit.

## Commit invariant

Each implementation commit updates the relevant R1–R4 task and leaves the build,
corpus gates, and style checks green. Unsupported constructs remain explicit data and
diagnostics; they never become `sorry`, an implicit axiom, or an unrelated identifier.
