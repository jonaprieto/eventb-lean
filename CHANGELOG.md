# Changelog

## 4.0.10 — 2026-08-15

- Re-derive strict POG obligations from the complete Rodin model-artifact closure,
  including theory environments, before accepting imported status evidence.
- Label declared external/SMT metadata, structurally checked Rodin imports, and
  axiom-bearing kernel replay separately from unproved obligations.
- Add compositional invariant and refinement contracts for event-local simulation and
  pre-state parallel assignment semantics.
- Add explicit frame, gluing, merged-event, witness, variant, and translated-sequent
  semantic contracts with positive and negative kernel-checked fixtures.
- Extend the bounded typed evaluator with finite relation application, image,
  domain/range restriction/subtraction, and override, with malformed and
  duplicate-function cases failing closed.
- Add source-bound parameterized enabled-event semantics, finite witness-domain
  completeness, and well-founded variant contracts with focused positive and negative
  fixtures; retain explicit fail-closed boundaries for unbounded binders and arbitrary
  formula interpretation.

## 4.0.9 — 2026-08-13

- Pin every first-party dependency to its newest released tag.

## 4.0.8 — 2026-08-13

- Centralize lexical typing-environment scopes for binders and event parameters.

## 4.0.7 — 2026-08-13

- Publish the dependency-graph README cleanup.

## 4.0.6 — 2026-08-13

- Totalize the pure AST dump recursion and classify operational partiality.

## 4.0.5 — 2026-08-12

- Adopt Lean v4.33.0, ProofWidgets v0.0.108, and precommit-lean v0.1.6.

## 4.0.4

- Consume Argus `v0.5.0` so command metadata and completion contracts use the
  published spec-driven CLI library.

## 4.0.3

- Preserve the Event-B corpus and refinement gates while auditing partiality.
