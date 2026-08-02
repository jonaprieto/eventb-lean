# Roadmap

`eventb-lean` v2 is tagged and the four GitHub issues found during the audit are
closed. The next work is not a new parser or a second model representation. It is
precision in proof-obligation generation followed by replayable proof evidence.

The architecture and dependency rules for this roadmap live in
[`notes/architecture.md`](notes/architecture.md). This file is the execution ledger.

## Current measured state

Run `lake exe gates --histogram` before changing a rule. The current ratchet is:

| Phase | Result | Meaning |
| --- | ---: | --- |
| P0 reader | 38/38 | Every pinned source file is read losslessly. |
| P1 formulas | 1102/1102 | Corpus formulas parse and round-trip. |
| P2 types | 940/940 | Rodin's recorded identifier types are reproduced. |
| P3 names | 1133/1133 | Every Rodin PO name is generated. Extra names remain visible. |
| P3b statements | 1129/1523 | 394 generated targets lack `.bpo` sequents. |
| P3b hypotheses | 1129/1523 | Comparable hypothesis sets are derived; the same 394 are unmatched. |
| P4 local baseline | 73/1133 | Deterministic evidence is attached as external-trusted. |

The 394 P3b unmatched records are not proof failures. They are generator-precision
work, grouped by the current histogram as 214 WD, 103 INV, 69 SIM, and 8 GRD. Seven
additional WFIS names are absent from the pinned `.bpo` files and remain explicit
coverage data rather than being forced into the P3b denominator. P4 has no kernel,
SMT, or imported-Rodin entries yet; the other 1060 obligations remain unproved.

## Completed foundation

- [x] Read Rodin `.bum`/`.buc` files losslessly and pin the corpus manifest.
- [x] Parse and type-check the pinned formula corpus.
- [x] Generate the 1133 Rodin obligation names and retain extra generated names in
  the ratchet instead of hiding them.
- [x] Read Rossi `.eventb` projects through the shared model and scope checker.
- [x] Support native contexts, machines, theories, datatypes, definitions, and rules.
- [x] Translate supported formulas and explicit theory bindings to Lean terms.
- [x] Replay kernel evidence and reject stale, forged, or mislabelled artifacts.
- [x] Display models, obligations, hypotheses, goals, and trust in CLI and
  ProofWidgets.
- [x] Keep the private book export and its images outside distribution artifacts.
- [x] Tag `prototype-v1.0.0` and `prototype-v2.0.0`.

## Version 3A: exact P3b coverage

Goal: make every generated statement/hypothesis correspond to a Rodin sequent, or
classify the absence as an intentional, named compatibility limitation. Do not bless
new baselines until the generated rule is explained and a negative control exists.

### A0. Coverage observability

- [x] Add a stable P3b coverage record containing component, event, PO kind, PO name,
  derivation status, and reason (`matched`, `no-sequent`, `goal-differs`, or
  `hypotheses-differ`).
- [x] Make `gates --histogram` group unmatched records by component and class, not
  only by failure text.
- [x] Keep WFIS/WWD's hypothesis-only Rodin shape explicit in CLI, JSON, widgets,
  and the ratchet.
- [x] Add a small negative-control check proving that deleting a gold sequent is
  reported as coverage loss rather than silently removed from the denominator.

Acceptance: `lake exe gates --coverage` identifies every P3b mismatch without opening a TSV
by hand; the current histogram remains reproducible.

### A1. Well-definedness precision

- [ ] Compare the 214 extra WD records against Rodin's WD generation conditions.
- [ ] Audit `wdRequired`, total-symbol metadata, theorem predicates, inherited guards,
  invariant WD, action WD, and witness WWD independently.
- [ ] Correct the shared condition in `EventB/POG.lean`; do not add per-component
  exceptions.
- [ ] Add one positive and one negative corpus-shaped regression for each corrected WD
  rule, including a total theory symbol and a partial application.

Acceptance: the 214 WD unmatched records reach zero, with no P0–P3 regression and no
new unmatched class.

### A2. Invariant precision

- [ ] Audit the 103 extra INV records against assigned-variable detection, inherited
  actions, refinement chains, theorem invariants, and parallel assignments.
- [ ] Separate a genuinely changed after-state from an invariant that only appears in
  the visible environment.
- [ ] Add negative controls for an untouched variable, an inherited assignment, and a
  refinement with a repeated event label.

Acceptance: the 103 INV unmatched records reach zero and every retained INV has a
matching Rodin sequent and comparable goal/hypotheses.

### A3. Refinement precision

- [ ] Audit the 8 extra GRD records for repeated concrete guards, event extension, and
  abstract-event lookup.
- [ ] Audit the 69 extra SIM records for inherited actions, parallel assignments,
  function override, and action labels.
- [ ] Add paired tests where a concrete event repeats an abstract guard/action and
  where it genuinely strengthens/simulates it.
- [ ] Verify substitution is simultaneous and witness substitution does not alter
  unrelated INV/GRD obligations.

Acceptance: GRD and SIM unmatched records reach zero, and the P3 name gate still
matches all 1133 Rodin names.

### A4. Witness coverage

- [ ] Keep WFIS existential generation for witnesses with a matching Rodin target.
- [ ] Keep WWD as a hypothesis-only obligation when Rodin supplies no target
  predicate; never invent a goal merely to raise a percentage.
- [ ] Add an openETCS-shaped fixture with both WFIS and WWD and assert the exact JSON
  coverage fields.
- [ ] Re-run the AMAN and ERTMS corpus after A1–A3; bless only reviewed improvements.

Acceptance: WFIS/WWD are either statement-checked or explicitly named as unsupported;
no witness obligation disappears from the report.

### A5. P3b release gate

- [ ] Reach zero unexplained `no-sequent` and `goal/hypotheses-differ` records.
- [ ] Update `baseline/statement.tsv`, `baseline/hypothesis.tsv`, README badges, and
  `notes/architecture.md` only after the gate diff is reviewed.
- [ ] Add a corpus negative control that breaks one POG rule and makes the gate fail.

Definition of done: P3b is exact for the supported Rodin PO surface, and every
unsupported surface is a named diagnostic with a regression test.

## Version 3B: proof evidence coverage

Goal: increase P4 without weakening the trust contract. A higher count is useful only
when the ledger says exactly who checked the result.

### B0. Canonical proof input

- [ ] Make every P3-matched obligation expose one canonical translated sequent or one
  actionable translation diagnostic.
- [ ] Include model scope, theory roots, normalized hypotheses, goal, and formula
  language version in the proof fingerprint.
- [ ] Ensure changing a source range or display label does not change the fingerprint,
  while changing semantics does.

Acceptance: the same obligation has byte-stable proof input across CLI, widgets, and
the replay backend.

### B1. Kernel-backed basic rules

- [ ] Move `true`, exact-hypothesis, reflexive, and contradiction discharge from the
  external local baseline to replayed Lean proof terms where translation permits.
- [ ] Preserve the current external backend as a separate comparator until kernel
  replay has an independent negative test.
- [ ] Add tests for wrong types, wrong hypotheses, changed goals, and stale fingerprints.

Acceptance: any new kernel count is backed by `Trust.Replay`; no external result is
relabelled as kernel evidence.

### B2. Structural logical reasoning

- [ ] Add auditable kernel proof construction for conjunction, implication, and
  hypothesis projection.
- [ ] Normalize only semantics-preserving formula structure; retain source formulas
  for diagnostics.
- [ ] Handle substituted invariant goals and witness feasibility without treating
  axioms as proved theorems.

Acceptance: each rule has a Lean proof-term regression and a negative control that
rejects a false implication.

### B3. Arithmetic and set reasoning

- [ ] Measure the remaining P4 failures by formula shape before implementing rules.
- [ ] Add the smallest kernel-checked arithmetic rules first, then membership,
  equality, subset, finite-set, and relation rules.
- [ ] Use solver output only behind an explicit SMT/external evidence mode; never turn
  solver success into kernel evidence without replay.
- [ ] Record rule labels and proof-input fingerprints in the ledger.

Acceptance: every new discharge rule improves a measured class and has a corresponding
negative test; P4 regressions fail CI.

### B4. Theory and refinement evidence

- [ ] Replay theory definitions, constructors, rewrite rules, and theorem/inference
  premises through their existing `Theory.Embed` obligations.
- [ ] Connect refinement semantics to translated INV, GRD, and SIM sequents only when
  explicit Lean bindings exist.
- [ ] Keep axiomatic definitions and imported Rodin statuses visible as assumptions,
  not kernel proofs.

Acceptance: theory-backed evidence identifies its declaration path, dependencies, and
trust mode in CLI and ProofWidgets.

### B5. P4 release gate

- [ ] Compare kernel, SMT, Rodin-imported, external, and unproved counts separately.
- [ ] Keep the Rodin `.bps` 1088 automatic / 45 manual result as a comparator, not as
  a proof target or trust upgrade.
- [ ] Record a timestamped benchmark with toolchain version and corpus SHA for every
  meaningful P4 change.

Definition of done: every discharged obligation has replayable or explicitly
classified evidence; all other obligations remain visibly unproved.

## Version 3C: usability and interoperability follow-up

These items depend on the P3b and P4 contracts and must not create a second checker.

- [ ] Add a widget view that filters by coverage status, proof mode, and PO class.
- [ ] Add source links from a PO to the model declaration and generated formula.
- [ ] Add a machine-readable project report combining P3b coverage and the trust ledger.
- [ ] Add optional `.tuf` theory I/O only for declarations with a faithful native
  representation and explicit rejection paths for the rest.
- [ ] Re-run all executable examples, including `WidgetDemo.lean`, after each UX change.

## Commit and audit protocol

Each implementation item is a focused commit. Every commit must pass:

```sh
lake build
lake build Examples
lake exe gates
scripts/style-check.py
git diff --check
```

Before declaring a phase complete:

1. inspect `lake exe gates --histogram`;
2. run a positive and negative control;
3. update this ledger, the architecture note, README badges, and generated `STATUS.md`;
4. record the corpus SHA and benchmark metadata when P4 changes;
5. verify no private book, image, archive, or generated build artifact is staged.

No item in this roadmap permits `sorry`, an implicit axiom, silently ignored syntax,
or an evidence mode that is stronger than the checker actually performed.
