# Native Event-B development environment

The native Lean/Event-B environment is the source of truth. Rodin artifacts are
compatibility input/output only; no runtime Rodin dependency is allowed.

## Core language and environment

- [ ] Define the core Event-B prelude (`BOOL`, `TRUE`, `FALSE`, `ℤ`, `ℕ`, and
  core operators) in one registry.
- [ ] Define `TheoryEnv` for the prelude, imported theories, and model scope.
- [ ] Give every symbol a stable identity, type, documentation, and source range.
- [ ] Specify conflict and shadowing rules against Event-B visibility semantics.

## Native theory authoring

- [ ] Add native Lean syntax for theory declarations and theory imports.
- [ ] Support operators, predicates, datatypes, and axiomatic definitions.
- [ ] Support typing and well-definedness rules.
- [ ] Support rewrite rules, inference rules, and polymorphic theorems.
- [ ] Validate theory soundness with generated proof obligations.

## Theory-aware toolchain

- [ ] Make lexing, parsing, AST resolution, typing, WD, and pretty-printing
  theory-aware.
- [ ] Make POG and prover backends consume resolved theory declarations.
- [ ] Preserve unsupported constructs as explicit diagnostics, never silently
  treating them as ordinary identifiers.

## Lean embedding and translation

- [ ] Embed resolved Event-B types, expressions, predicates, and theories in Lean.
- [ ] Translate definitions and datatypes to kernel-checkable Lean declarations.
- [ ] Represent axiomatic assumptions without hiding them as trusted theorems.
- [ ] Record kernel, SMT, Rodin-imported, and external trust in the ledger.

## Native UX and project tooling

- [ ] Add project/theory dependency loading and validation commands.
- [ ] Add hover and Go-to-Definition for prelude and theory symbols.
- [ ] Add theory/source/trust views to ProofWidgets.
- [ ] Add native examples covering a Boolean theory and an imported operator.

## Compatibility and verification

- [ ] Keep the existing Rodin corpus reader and gates green throughout.
- [ ] Add optional Rodin theory import/export after native theories work.
- [ ] Add negative tests for scope, conflicts, typing, WD, and theory visibility.
- [ ] Add LSP tests for user, prelude, and theory definitions.
- [ ] Run `lake build`, `lake exe gates`, and `scripts/style-check.py` before
  every commit.

## Commit milestones

- [ ] Core prelude and symbol registry.
- [ ] Theory environment and native declarations.
- [ ] Theory-aware parser, checker, WD, and POG.
- [ ] Lean embedding and translation.
- [ ] Native widgets and project tooling.
- [ ] Rodin compatibility and final audit.
