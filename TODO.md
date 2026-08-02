# Roadmap

`eventb-lean` v3 is tagged and the four GitHub issues found during the audit are
closed. The next work is production hardening, not a new parser or a second model
representation: every supported surface must be exercised, every limitation must be
visible, and every accepted proof result must retain its trust classification.

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
| P3b statements | 1129/1322 | 193 generated targets lack `.bpo` sequents. |
| P3b hypotheses | 1129/1322 | Comparable hypothesis sets are derived; the same 193 are unmatched. |
| P4 local baseline | 73/1133 | Deterministic evidence is attached as external-trusted. |

The 193 P3b unmatched records are not proof failures. They remain explicit coverage
data with diagnostics: 103 are pinned-`.bpo` omissions of plain type invariants; the
rest are omissions in definedness, refinement, or witness-feasibility classes. Seven
additional WFIS names are absent from the pinned `.bpo` files and remain explicit
coverage data rather than being forced into the P3b denominator. P4 has no corpus
kernel, SMT, or imported-Rodin entries yet; the other 1060 obligations remain unproved.

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
- [x] Tag `prototype-v1.0.0`, `prototype-v2.0.0`, and `prototype-v3.0.0`.

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

- [x] Compare the 214 extra WD records against Rodin's WD generation conditions.
- [x] Audit `wdRequired`, total-symbol metadata, theorem predicates, inherited guards,
  invariant WD, action WD, and witness WWD independently.
- [x] Correct the shared condition in `EventB/POG.lean`; do not add per-component
  exceptions.
- [x] Add one positive and one negative corpus-shaped regression for each corrected WD
  rule, including a total theory symbol and a partial application.

Progress: assignment WD now inspects only the right-hand side, and event-level
invariant WD is no longer emitted as a separate obligation. The corpus moved from
214 to 13 unmatched WD names; the remaining records are guard definedness cases.
`examples/Counter.lean` covers a partial `card` RHS positively and a function-update
LHS negatively.

Acceptance: the corrected shared rules are regression-tested; the 13 remaining guard
records are reported as `pinned-bpo-omits-definedness-sequent` until source Rodin
regeneration establishes a different rule.

### A2. Invariant precision

- [x] Audit the 103 extra INV records against assigned-variable detection, inherited
  actions, refinement chains, theorem invariants, and parallel assignments.
- [x] Separate a genuinely changed after-state from an invariant that only appears in
  the visible environment.
- [x] Add negative controls for an untouched variable, an inherited assignment, and a
  refinement with a repeated event label.

Progress: all 103 records satisfy the assigned-variable rule, but the pinned `.bpo`
selectively omits their INV sequents. Coverage reports
`pinned-bpo-omits-plain-type-invariant`; the broad skip experiment failed P3 recall.

Acceptance: no unsound skip rule is introduced; exact parity requires regenerated
upstream `.bpo` files or an explicitly selected compatibility mode.

### A3. Refinement precision

- [x] Audit the 8 extra GRD records for repeated concrete guards, event extension, and
  abstract-event lookup.
- [x] Audit the 69 extra SIM records for inherited actions, parallel assignments,
  function override, and action labels.
- [x] Add paired tests where a concrete event repeats an abstract guard/action and
  where it genuinely strengthens/simulates it.
- [x] Verify substitution is simultaneous and witness substitution does not alter
  unrelated INV/GRD obligations.

Progress: SIM now consumes direct concrete actions while INV keeps the full inherited
state substitution. The earlier abstract-action filter was rejected because it removed
two required Rodin names. The remaining 69 SIM and 8 GRD records are classified as
pinned-`.bpo` omissions; no generic inheritance exception is safe without regenerated
Rodin output.

Acceptance: GRD/SIM mismatches are named and regression-tested; exact parity requires
regenerated upstream `.bpo` files or an explicitly selected compatibility mode.

### A4. Witness coverage

- [x] Keep WFIS existential generation for witnesses with a matching Rodin target.
- [x] Keep WWD as a hypothesis-only obligation when Rodin supplies no target
  predicate; never invent a goal merely to raise a percentage.
- [x] Add an openETCS-shaped Rossi fixture with both WFIS and WWD and assert the exact
  JSON fields through `eventb check --json`; `eventb report` also carries both records
  into the trust report.
- [x] Re-run the AMAN and ERTMS corpus after A1–A3; bless only reviewed improvements.

Acceptance: WFIS/WWD are either statement-checked or explicitly named as unsupported;
no witness obligation disappears from the report.

### A5. P3b release gate

- [x] Reach zero unexplained `no-sequent` and `goal/hypotheses-differ` records.
- [x] Review `baseline/statement.tsv`, `baseline/hypothesis.tsv`, README badges, and
  `notes/architecture.md` against the post-A1–A3 gate diff; no bless was needed because
  the ratchet did not gain or lose a record.
- [x] Add a corpus negative control that breaks one POG rule and makes the gate fail.

Definition of done: P3b is exact for the supported Rodin PO surface, and every pinned
corpus compatibility difference is a named diagnostic with a regression test.

## Version 3B: proof evidence coverage

Goal: increase P4 without weakening the trust contract. A higher count is useful only
when the ledger says exactly who checked the result.

### B0. Canonical proof input

- [x] Make every P3-matched obligation expose one canonical translated sequent through
  `Trust.Replay`, or the actionable `requires-explicit-bindings` diagnostic in the
  machine-readable report.
- [x] Include model scope, theory roots, normalized hypotheses, goal, and formula
  language version in the proof fingerprint.
- [x] Ensure changing a source range or display label does not change the fingerprint,
  while changing semantics does.

Progress: `Obligation.canonical` is independent of display name/kind and contains
scope, theory roots, normalized sequent, and formula-language version. The translated
sequent still has one path through `Trust.Replay.translateStatement`; the remaining
work is to expose its success or translation error in the machine-readable report.

Acceptance: the same obligation has byte-stable proof input across CLI, widgets, and
the replay backend; corpus proof automation still requires explicit semantic bindings.

### B1. Kernel-backed basic rules

- [x] Move `true`, exact-hypothesis, reflexive, and contradiction discharge from the
  external local baseline to replayed Lean proof terms where translation permits.
- [x] Preserve the current external backend as a separate comparator until kernel
  replay has an independent negative test.
- [x] Add tests for wrong types, wrong hypotheses, changed goals, and stale fingerprints.

Acceptance: every kernel result in native examples is backed by `Trust.Replay`; no
external result is relabelled as kernel evidence.

### B2. Structural logical reasoning

- [x] Add auditable kernel proof construction for conjunction, implication, and
  hypothesis projection.
- [x] Normalize only semantics-preserving formula structure; retain source formulas
  for diagnostics.
- [x] Handle substituted invariant goals and witness feasibility without treating
  axioms as proved theorems.

Acceptance: each implemented structural rule has a Lean proof-term regression and a
negative control that rejects a false implication. Compound arithmetic/set goals remain
explicitly unproved.

### B3. Arithmetic and set reasoning

- [x] Measure the remaining P4 failures by formula shape before implementing rules.
- [x] Add the smallest kernel-checked arithmetic rule first: positive closed numerals
  use a replayed Lean proof and declare its standard `propext` dependency.
- [x] Define the post-prototype extension boundary for membership, equality, subset,
  finite-set, and relation goals: each shape needs a replayable proof and negative
  control before it enters the kernel backend.
- [x] Keep solver output behind an explicit SMT/external evidence mode; never turn
  solver success into kernel evidence without replay.
- [x] Record local rule labels and proof-input fingerprints in the machine-readable
  report; kernel replay reports its declaration and axiom metadata.

Acceptance: every new discharge rule improves a measured class and has a corresponding
negative test; P4 regressions fail CI.

### B4. Theory and refinement evidence

- [x] Replay explicit theory definition, datatype, and rule instances through
  `Theory.Embed` and `Trust.Replay`; generic soundness obligations remain open data.
- [x] Connect refinement evidence to translated INV, GRD, and SIM sequents only when
  explicit Lean bindings exist; `WidgetDemo.lean` exercises that path.
- [x] Keep axiomatic definitions and imported Rodin statuses visible as assumptions,
  not kernel proofs.

Acceptance: theory-backed evidence identifies its declaration path, dependencies, and
trust mode in examples and the report; open theory soundness is never hidden.

### B5. P4 release gate

- [x] Compare kernel, SMT, Rodin-imported, external, and unproved counts separately.
- [x] Keep the Rodin `.bps` 1088 automatic / 45 manual result as a comparator, not as
  a proof target or trust upgrade.
- [x] Record a timestamped benchmark with toolchain version and corpus SHA for every
  meaningful P4 change.

Definition of done: every discharged obligation has replayable or explicitly
classified evidence; all other obligations remain visibly unproved.

## Version 3C: usability and interoperability follow-up

These items depend on the P3b and P4 contracts and must not create a second checker.

- [x] Present PO classes as expandable widget sections with coverage status and proof
  mode badges; interactive client-side filtering is a post-prototype enhancement.
- [x] Preserve Lean source navigation for native declarations and show the generated
  formula beside each PO; raw XML/Rossi source ranges remain an explicit limitation.
- [x] Add a machine-readable project report combining P3 name coverage and the trust
  ledger, with explicit translation diagnostics.
- [x] Add `.tuf` theory import/export only for declarations with a faithful native
  representation and explicit rejection paths for the rest.
- [x] Re-run all executable examples, including `WidgetDemo.lean`, after the reporting
  and trust UX changes.

The first prototype has no unowned implementation items. The remaining ceilings are
deliberate: exact P3b parity for the 193 pinned `.bpo` omissions needs regenerated Rodin
artifacts or an explicit compatibility mode, and corpus-scale kernel proof counts need
semantic Lean bindings for each model symbol. Both are reported rather than silently
claimed as complete. The next proof increments are measured by the P4 formula-shape
histogram, starting with membership and subset goals.

## Version 4: production readiness

This is the release contract for the first commit that may be called
production-ready. Production-ready does not mean that every obligation is automated;
it means that supported inputs are checked reproducibly, unsupported inputs fail
clearly, generated obligations are measured against the available oracle, and no proof
or trust result is presented as stronger than the evidence behind it.

Every V4 item has one GitHub issue labelled `production-readiness`. An item is complete
only when its implementation is committed, the checklist records the solving commit,
and the issue is closed with that same commit SHA in the closing comment.

### V4.0 Release definition

- [x] #5 Write the supported-input contract for Rodin XML, Rossi `.eventb`, native Lean
  DSL, native theories, and the supported `.tuf` subset.
- [x] #6 Define the production P3b and P4 release thresholds explicitly; do not use a
  larger percentage as a substitute for exact diagnostics or trustworthy evidence.
- [ ] #7 Update README badges, `STATUS.md`, `notes/architecture.md`, and release notes
  from the final measured commit before tagging.
- [ ] #8 Tag the release only after every V4 checklist item is checked and the complete
  verification command succeeds from a clean checkout.

Production thresholds:

- P0, P1, P2, and P3 must remain exact against the pinned corpus.
- P3b must have no unexplained `goal-differs` or `hypotheses-differ` records. Every
  generated target without a pinned `.bpo` sequent must either be exact after artifact
  regeneration or carry a named, tested compatibility decision.
- P4 has no arbitrary percentage gate. Every discharged result must have replayable or
  explicitly classified evidence, evidence modes must not regress, and every remaining
  obligation must stay visibly `unproved`.
- A production report must publish the measured P3b/P4 counts and trust-mode breakdown;
  a larger discharge percentage cannot compensate for hidden mismatches or unverifiable
  evidence.

### V4.1 CI and executable-surface coverage

- [x] #9 Make CI build every shipped target: `EventB`, `EventBWidgets`, `Examples`,
  `gates`, `rossi-dump`, `eventb`, and `bench`.
- [x] #10 Run the CLI fixture matrix in CI, including `check --json`, `summary`, `report`,
  `po`, `prove`, `theory`, and the expected error paths for invalid arguments and
  missing components.
- [x] #11 Run `rossi-dump` over every checked-in `.eventb` fixture and assert the complete
  component list, names, and success status.
- [x] #12 Add machine-readable assertions for the witness fixture: exact INV, GRD, SIM,
  WD, WFIS, and hypothesis-only WWD records, including exit status.
- [x] #13 Make the full verification contract fail on a missing executable target rather
  than relying on the default Lake target to discover it indirectly.
- [x] #14 Record whether the official Rossi differential executable is available in CI;
  a production release must either run the comparison or fail with an actionable
  dependency error.

### V4.2 Book-example correctness

- [x] #15 Replace the 21 book-example `POG.generate ... .isEmpty == false` smoke checks in
  `BookBridge.lean`, `BookPrograms.lean`, and `BookSystems.lean` with exact assertions
  for selected obligation names, classes, goals, and hypotheses.
- [x] #16 Cover at least one exact expected obligation for each book family: bridge,
  file-transfer, notation/program, controller/system, refinement, witness, and
  convergence examples.
- [x] #17 Add negative controls proving that a changed or missing obligation fails the
  example test instead of merely leaving a non-empty list.
- [x] #18 Keep the private book export, images, and archive outside commits and release
  artifacts; retain only section references and independently authored executable
  models.

### V4.3 P3b parity and compatibility

- [x] #19 Resolve the 193 unmatched P3b records against regenerated Rodin `.bpo` artifacts,
  or implement an explicit compatibility mode for the pinned omissions.
- [x] #20 Preserve the current diagnostics for plain type invariants, definedness,
  refinement guards/actions, and witness feasibility while resolving the records.
- [x] #21 Keep goal and hypothesis comparison separate from PO-name comparison; no missing
  sequent may be hidden by shrinking a denominator or broadening a skip rule.
- [x] #22 Add a regression fixture and negative control for every compatibility rule that
  changes the P3b result.
- [x] #23 Require `lake exe gates --coverage` and `lake exe gates --histogram` to remain
  reproducible after each P3b change.

### V4.4 P4 proof coverage and trust

- [x] #24 Bind corpus symbols to explicit Lean semantic values in a reviewable way before
  claiming corpus-scale kernel coverage.
- [x] #25 Implement the next prover rules in measured histogram order, starting with
  membership and subset goals, then equality, finite sets, relations, and arithmetic
  only where replayable proof terms are available.
- [x] #26 Give every new rule a positive proof-term replay test, a false-goal negative
  control, and a stale/fingerprint mismatch test.
- [x] #27 Keep kernel, SMT, Rodin-imported, external, and unproved modes separate in the
  ledger, CLI, widgets, and reports.
- [x] #28 Ensure every discharged result identifies its declaration or verifier, input
  fingerprint, dependencies, and trust mode; no external result may be relabelled as
  kernel evidence.
- [x] #29 Re-measure P4 against the pinned corpus and record the toolchain and corpus SHA
  in a timestamped benchmark after each prover increment.

### V4.5 Rossi fixture quality

- [x] #30 Document `actions.eventb` and `boundaries.eventb` explicitly as parser-boundary
  fixtures, including their intentional semantic typechecking failures.
- [x] #31 Separate parser-only fixtures from semantically valid project fixtures, or add
  an executable expectation file that records the intended exit code and diagnostic.
- [x] #32 Add `witnesses.eventb` to `scripts/rossi-diff.py` once the official Rossi parser
  accepts the same construct; otherwise record the incompatibility explicitly.
- [x] #33 Pin or provision the official Rossi executable used by the differential matrix;
  do not leave compatibility confidence dependent on an unmentioned local install.

### V4.6 ProofWidget and editor acceptance

- [ ] #34 Manually verify `examples/WidgetDemo.lean` in the VS Code Infoview from a clean
  Lean server: model panels, obligation sections, hypotheses, goals, proof badges, and
  the 11 replayed entries must render without React or widget errors.
- [ ] #35 Verify native Go to Definition and scope diagnostics for theory, context, machine,
  event, and invariant symbols in the editor.
- [x] #36 Record the manual UI acceptance procedure in the README without committing
  private screenshots or generated editor state.
- [x] #37 Keep raw Rossi/XML source-range limitations explicit until source navigation for
  those front ends is implemented and tested.

### V4.7 Distribution and operational gate

- [x] #38 Run the complete build, gate, fixture, style, manifest, and diff checks from a
  clean checkout with no private book artifacts staged.
- [x] #39 Replace the current full-scope `GRIP_TOKEN` CI credential with the read-only
  `GRIP_SSH_KEY` deploy key before the production release.
- [x] #40 Verify the corpus manifest, pinned dependency SHAs, generated status, benchmark
  metadata, and README badges all describe the same commit.
- [ ] #41 Confirm that no `sorry`, implicit axiom, silently ignored syntax, stale evidence,
  or unclassified unsupported construct is reachable through a shipped front end.
- [x] #42 Publish a release note that states the supported subset, current P3b/P4 numbers,
  trust modes, known ceilings, and the exact commands used for acceptance.

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
