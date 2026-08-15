# Accuracy roadmap

The implementation is being hardened for refinement-heavy Event-B, not merely tuned
to the pinned corpus. Unsupported syntax, unresolved references, untyped assignments,
incomplete POG semantics, and unverifiable evidence must fail closed and remain visible
in reports. No second model representation is planned.

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
| P3b statements | 1132/1325 | Derived goals are compared; 200 pinned compatibility omissions remain tracked. |
| P3b hypotheses | 1132/1325 | Derived hypotheses are compared; 200 pinned compatibility omissions remain tracked. |
| P3b WWD | 1/1 | Hypothesis-only witness well-definedness is scored separately. |
| P3b compatibility | 200 pinned | Named, regression-tested omissions in the pinned `.bpo` oracle. |
| P4 local baseline | 73/1133 | Deterministic evidence is attached as external-declared. |

The 200 P3b compatibility records are not proof failures. They are explicit coverage
data classified by kind, preserved in `baseline/compatibility.tsv`, and rejected if a
new unexplained mismatch appears. P4 has no corpus kernel, SMT, or imported-Rodin
entries yet; the other 1060 obligations remain unproved.

## Accuracy campaign: general refinement-heavy Event-B

Status: active. This campaign supersedes prototype-completion claims where adversarial
review found that an internally consistent gate was weaker than the semantic or trust
contract. The target is fail-closed, structurally faithful support for a documented
refinement-heavy Event-B subset; passing the pinned corpus alone is not completion
evidence.

### Current blockers

- [x] Fail on missing component/event/theory references instead of treating them as empty
  closures.
- [x] Keep typing and parse diagnostics attached to POG generation; checked generation
  rejects any diagnostic.
- [x] Validate assignment arity/lvalues, primed closure in `:∣`, duplicate targets, and
  initialization legality; strict checked generation rejects unresolved diagnostics.
- [x] Separate compatibility-scope inference from strict Event-B parameter scope:
  concrete guards/actions must not inherit abstract parameters without a witness.
- [x] Include deterministic, nondeterministic, inherited, and stuttering action semantics
  in the strict invariant/refinement POG path; keep the pinned corpus projection isolated.
- [x] Generate witness WFIS/WWD and FIS shapes, with witness predicates retained where
  they are semantic hypotheses; score WWD independently.
- [x] Add numeric/set variants, anticipated/convergent relations, and default constant
  variants for machines containing anticipated events.
- [x] Correct relation subtraction, strict subset, exponentiation, and corresponding WD
  rules in the formula translator.
- [x] Reject open metavariable kernel proofs and bind accepted evidence to the exact
  canonical obligation; Rodin status imports must be parsed from the supplied artifact.
- [x] Close the supported generality ceiling: bind the named frame, gluing, merge,
  witness, and variant contracts in `EventB.Semantics`, and the explicit sequent
  adapters in `EventB.POGSoundness`, to the generated POG classes that have a typed
  evaluator path. The closed POG-class table, source-bound adapters, parameterized
  enabled-event contract, finite witness-domain evaluator, and well-founded VAR
  contract have kernel-checked positive/negative fixtures. Unsupported
  partial/theory applications, unrestricted binders/comprehensions, and automatic
  interpretation of arbitrary formulas remain explicit fail-closed boundaries.

### Vertical-slice order

1. Resolution, scopes, and fail-closed diagnostics — implemented and negative-tested.
2. Typed assignments and refinement event relations — component-bound typed deterministic
   assignments, explicit before/after valuation, parameterized event semantics, and
   source-indexed merge/frame edge cases are implemented.
3. Formula translation and definedness — implemented and corpus-gated.
4. Witnesses and variant POG classes — implemented for the supported syntax.
5. Semantic soundness theorems for each supported POG class — generic contracts,
   source-bound model bindings, and typed evaluator lemmas are present; unsupported
   formula families remain fail-closed rather than being assigned guessed semantics.
6. Trust/provenance hardening — implemented for local and parsed Rodin paths; digest
   strength and external verifier execution remain explicit trust boundaries.
7. Independent differential tests, release evidence, and adversarial review — active
   until the final clean-checkout campaign passes.

Each slice requires a minimal positive model, a negative model, a Rodin-shaped
comparison, a full build, and a fresh adversarial review before its checkbox is marked.

### Generality-ceiling execution plan

The following is the verified supported path. Each item is evidence for the accepted
subset; the explicit unsupported boundaries are part of the contract rather than
promises of arbitrary-term automation.

1. **Typed semantic adapter (bounded slice now verified).** `EventB.POGSoundness` now
   interprets closed arithmetic, Boolean logic, finite sets, maplets, typed membership,
   subset, unary negation, and simultaneous deterministic assignment through one
   `Except EvalError` path. Finite-set equality is extensional; ill-typed, unbound,
   overloaded-comma, partial, and unsupported terms fail explicitly; WWD is a separate
   hypothesis-only validity shape. `ComponentValuation` now reuses the strict recursive
   `Typing.Ty` environment, binds writable variables and effective event assignments,
   requires explicit finite carrier observations for given-set atoms, and rejects
   typing diagnostics before valuation. Caller-controlled fuel is threaded through
   public evaluator wrappers; primed evaluation is private to the declaration-checked
   `CheckedBeforeAfter` path. The adapter accepts typed state valuation validity for
   `THM`, `WD`, `VWD`, and `WWD`, and typed before/after valuation validity for the
   supported transition classes. `evalPredicateOverFiniteDomain` provides a complete,
   source-independent witness boundary for caller-supplied finite candidate domains;
   unrestricted binder evaluation remains one-sided and fails closed when no domain is
   supplied. Finite relation application, image, domain/range
   restriction/subtraction, and override are now bounded and fail closed on non-functional or
   malformed relations; partial/theory applications and binder/comprehension semantics
   remain closed. Accepting formula and transition APIs also require a source locator
   over the project refinement closure in addition to exact generated-obligation
   membership. Acceptance requires a positive and negative sequent for each supported
   operator family, with a changed semantic term rejected.
2. **PO-family soundness.** Source-bound, proof-carrying adapter contracts now exist for
   INV/WD/GRD/SIM/THM/FIS/WFIS/WWD, EQL, MRG, VWD, and integer/finite variants; split merge
   and anticipated/convergent variant semantics are explicit. Exact model-derived,
   forged-goal-controlled fixtures now exercise THM, INV, GRD, SIM, FIS, WFIS, WWD,
   and an anticipated integer NAT/VAR pair.
   These contracts consume the exact checked `Obligation`, preserve its identity,
   bind exact component/event declarations and effective deterministic assignments where
   applicable, and require a checked `FormulaAdequacy` witness: validity of that exact
   generated sequent plus a formula-to-contract implication. The implication remains
   project-specific; there is no automatic interpretation of arbitrary Event-B terms.
   MRG target labels, VWD, FIN/EQL locator controls, and parsed guard provenance now
   have direct fixtures; `test/MrgAdapterFixtures.lean` additionally checks an exact
   generated two-target MRG transition bridge and ordered branch pairing. The bounded
   integer EQL adapter has a positive/negative source-and-sequent fixture, and FIN has
   a source-bound constant finite-set adapter witness plus typed powerset evaluator
   controls. MRG now has source-indexed target locators, exact branch guard/action
   pairings, and same-label foreign-branch negatives. A model-derived finite-set VAR
   fixture now uses the invariant-restricted source-indexed carrier; the legacy
   `FiniteSetVariantAdapter.actionTotal` remains a compatibility diagnostic rather
   than an acceptance path. `EnabledGuardFixtures` now covers a model-derived
   parameterized event, exact parameter declarations, positive/negative enabledness,
   and parameterized refinement simulation. Nondeterministic assignment relations are
   covered by the relational FIS fixture.
3. **Refinement state model.** Typed observations and explicit event parameters are
   now represented at the semantic boundary. Frame preservation, after-state gluing,
   simultaneous assignment, duplicate-target rejection, function override, stuttering,
   and merged-event counterexamples are source-bound or kernel-checked fixtures.
4. **Witness and variant semantics.** WWD has an exact source-bound adapter; WFIS has a
   bounded finite-domain evaluator boundary and explicit negative controls. Merge
   simulation has branch-specific abstract targets, and VAR is representable over an
   explicit well-founded relation.
   Keep anticipated non-increase separate from convergent strict decrease; VWD/NAT/FIN
   and finite-set source controls are present. Typed `ℙ(T)` evaluation, positive /
   negative evaluator fixtures, and a model-derived finite-set VAR fixture now exist;
   its domain carries both invariant hypotheses and exact source-measure
   correspondence. The legacy constant-variant witness remains only as a compatibility
   regression. Parameterized enabledness is covered for the accepted source-bound slice;
   arbitrary binders and comprehension terms remain unsupported by contract.
5. **Independent release ratchet.** Add the new class-level semantic checks to the CLI
   fixture matrix, run the exact Rossi differential in CI, rerun the manual editor gate,
   regenerate status from the final commit, then perform the clean-checkout command
   matrix. Only after that may V4 #7/#8 be checked and a release tag created.

### Evidence ledger

| Area | Current evidence | Status |
| --- | --- | --- |
| Build and existing gates | Lean 4.33 build; P0/P1/P2/P3 pass; P3b tracked | current |
| General refinement typing | AMAN/event-scope, hidden-parameter, primed-scope, duplicate-label, and missing-reference controls pass | current |
| POG semantic coverage | nondeterministic actions, data-refinement glue, WWD, variants, EQL/MRG provenance, named frame/gluing/merge/witness/variant contracts, parameterized enabledness, closed POG-class table, error-aware typed evaluator, explicit `POGSoundness` sequent validity, and model-derived THM/INV/GRD/SIM/FIS/WFIS/WWD/integer-NAT-VAR/finite-set-VAR/VWD fixtures | strict checked path; unrestricted binder/comprehension and arbitrary formula semantics remain explicitly unsupported |
| Kernel trust | replay checks reject open mvars, stale goals, forged axioms, and context drift | current |
| External/Rodin provenance | supplied model-artifact parsing, model-derived canonical POG binding, BPO/status identity, monotonic ledger update; legacy status-only replay rejected | current; exact closure and digest authenticity remain outside the contract |
| Release reproducibility | CLI fixture, gate status, and exact baseline ratchet are required | active |
| Official Rossi differential | pinned v0.1.7 SHA verified; x86_64 guest validates all four fixtures; CI provisions the exact differential command | current; CI remains release gate |

The ledger is updated after every implementation commit. A phase is not complete when
the build is green if a counterexample, oracle comparison, or adversarial review remains
unresolved.

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

Progress: the compatibility projection preserves the pinned right-hand-side rule;
strict checked generation also includes function-update arguments, and event-level
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
deliberate: exact P3b parity for the 200 pinned `.bpo` omissions needs regenerated Rodin
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

- [x] #19 Resolve the 200 unmatched P3b records against regenerated Rodin `.bpo` artifacts,
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
- [x] #32 Add `witnesses.eventb` to `tools/rossi-diff.py` once the official Rossi parser
  accepts the same construct; otherwise record the incompatibility explicitly.
- [x] #33 Pin or provision the official Rossi executable used by the differential matrix;
  do not leave compatibility confidence dependent on an unmentioned local install.

### V4.6 ProofWidget and editor acceptance

- [x] #34 Manually verify `examples/WidgetDemo.lean` in the VS Code Infoview from a clean
  Lean server: model panels, obligation sections, hypotheses, goals, and 11 explicitly
  declared evidence badges rendered without React or widget errors.
- [x] #35 Verify native Go to Definition and scope diagnostics for theory, context, machine,
  event, and invariant symbols in the editor. `#eventb_lsp_checks` verifies native source
  ranges for the declaration classes; after the DSL reference-location fix, VS Code Go to
  Definition from `sees LspContext` found the declaration, and a temporary unknown
  identifier reproduced the expected Lean diagnostic before the unsaved edit was discarded.
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
- [x] #41 Confirm that no `sorry`, implicit axiom, silently ignored syntax, stale evidence,
  or unclassified unsupported construct is reachable through a shipped front end.
- [x] #42 Publish a release note that states the supported subset, current P3b/P4 numbers,
  trust modes, known ceilings, and the exact commands used for acceptance.

## Commit and audit protocol

Each implementation item is a focused commit. Every commit must pass:

```sh
lake build
lake build Examples
lake exe gates
pre-commit run --all-files
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
