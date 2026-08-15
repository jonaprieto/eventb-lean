# Production acceptance

This note is the release checklist for the current accuracy campaign. It describes
the supported contract and measured ceilings; it does not claim that every proof
obligation is automatically discharged.

## Measured baseline

The current acceptance run uses Lean `v4.33.0`, ProofWidgets `v0.0.108`, and
`corpus/MANIFEST.tsv` SHA256
`c76a5dca92f0ea32f8c1e20e9da4cb88006bd048cee78d9fd66d03a20e664c45`.
The corpus itself remains pinned to the upstream commits recorded in the manifest.
The release candidate is accepted only after the clean-checkout command matrix below
passes; the current worktree is intentionally still under adversarial review.

| Gate | Result | Interpretation |
| --- | ---: | --- |
| P0 reader | 38/38 | Source files read losslessly. |
| P1 formulas | 1102/1102 | Formulas parse and round-trip. |
| P2 types | 940/940 | Recorded identifier types reproduced. |
| P3 obligations | 1133/1133 | Rodin PO names generated. |
| P3b statements | 1132/1325 | Derived goals and named compatibility omissions are tracked. |
| P3b hypotheses | 1132/1325 | Derived hypothesis sets and named compatibility omissions are tracked. |
| P3b WWD | 1/1 | Hypothesis-only witness well-definedness is scored separately. |
| P3b compatibility | 200 pinned | Explicit, classified pinned-oracle omissions. |
| P4 local baseline | 73/1133 | Explicit external-declared evidence; 1060 remain unproved. |

The P3b compatibility records are not silently omitted or counted as proof failures.
They are pinned, classified, regression-tested, and reported by the gates. The P4
count is a measured baseline, not a percentage claim. Kernel, SMT, and imported-Rodin
counts are zero for the corpus baseline; the local results remain external-declared.

## Supported surfaces

- Rodin `.bum` and `.buc` source models through the pinned XML/model reader.
- Rodin `.bpo` and `.bps` comparison and explicitly classified status inputs.
- Rossi `.eventb` projects, including the supported component, refinement, witness,
  variant, event-status, and formula subset.
- Native Lean contexts, machines, theories, datatypes, definitions, and rules.
- The faithful `.tuf` theory subset; unsupported declarations are rejected.
- Refinement-heavy Event-B within the checked subset: inherited actions, deterministic
  and nondeterministic assignments, witnesses, stuttering/SIM, EQL/MRG, and numeric/set
  variants. `generateChecked` is the strict path: it rejects unresolved references,
  duplicate labels, malformed component kinds, invalid primed scope, and hidden
  parameters after non-extended refinement boundaries. The corpus gate retains a
  documented compatibility projection for pinned Rodin omissions. The semantic slice
  also includes source-bound parameterized enabled events, finite witness domains, and
  well-founded variant contracts; these require explicit model/domain bindings.
- CLI reports, proof-obligation output, trust-ledger evidence, ProofWidgets, and
  native Lean declaration ranges.

Unsupported syntax is diagnosed rather than silently ignored. Raw Rossi/XML inputs do
not promise editor source ranges. The private book export, images, and archive are
local research inputs and are not release artifacts.

## Trust contract

Every obligation has an explicit ledger mode. Kernel evidence requires replayed Lean
proof terms and checked axiom metadata. SMT, Rodin-imported, and external evidence
remain their own modes with verifier, version, input digest, and fingerprint metadata.
Unproved obligations remain `unproved`; reports never upgrade them implicitly.
Rodin imports additionally require the supplied model-artifact set, shared project
parsing, strict model-derived POG regeneration (using the supplied theory environment),
explicit source-component identity (and agreement with the XML root name when present),
the named BPO sequent, and equality of its canonical obligation with the regenerated one,
plus an independently parsed proof-status record. Missing referenced components fail
closed; exact transitive-closure completeness and stale-artifact rejection remain
release follow-up work.
The current digest primitive remains an internal fingerprint, not a cryptographic
authenticity claim. Legacy status-only Rodin evidence is rejected; model, BPO, and
status provenance are mandatory. SMT and external verifier fields remain caller-supplied
metadata and are never presented as Lean-kernel replay; CLI JSON marks those records
`metadata_only: true`.

The bounded `EventB.POGSoundness` adapter is a separate, explicit valuation boundary:
it supports typed state-formula validity for `THM`, `WD`, `VWD`, and `WWD`, plus typed
before/after validity for the supported transition classes, in its documented subset;
`WFIS` has a finite-domain completeness lemma and a bounded witness-candidate fixture,
but general acceptance still requires a caller-supplied finite domain. It uses explicit
evaluator errors and definedness checks, and rejects unknown POG
classes, malformed identity/diagnostics, malformed WWD shapes, overloaded comma,
unsupported applications, and other unsupported constructs. The generic formula-model
acceptor is fail-closed until semantic adequacy is supplied. Finite relation application,
image, domain/range restriction/subtraction, and override are supported only for explicit
finite pair sets; duplicate function inputs and malformed relation members fail closed. The accepting
sequent APIs require membership in `POG.generateCheckedIn` plus a source-locator check
over the component's refinement closure; their `validUnchecked` counterparts are only
local evaluator fixtures and are not trust evidence. Refinement-heavy classes additionally
require the source-bound proof-carrying adapters in `EventB.POG.RefinementAdapters`.
Transition-formula adequacy takes the checked event relation as a type-level source
parameter and requires both source validity and source completeness. This prevents a
singleton evaluator domain from being substituted for a non-singleton Event-B action.
The accepting INV, GRD, SIM, and FIS fixtures use source-indexed subtype states; WFIS,
WWD, an anticipated integer NAT/VAR pair, and VWD have exact source-bound witnesses.
MRG has an exact generated two-target, source-transition, and ordered-branch fixture
(`test/MrgAdapterFixtures.lean`), including source-indexed branch guard/action exactness
and a same-label foreign-branch negative (`test/MrgSemanticFixtures.lean`). EQL has a
bounded source-complete integer adapter, and FIN has a source-bound constant finite-set
adapter witness plus typed powerset evaluator controls. The finite adapter now also has
a model-derived invariant-restricted source-domain fixture
(`test/FiniteVariantModelFixtures.lean`); `FiniteSetVariantAdapter.actionTotal` remains
a checked diagnostic of the legacy unrestricted VAR carrier. `CheckedGuardSource`
binds the parsed effective guard list; parameterized enabledness is accepted only for
the source-bound parameter/event slice covered by the fixtures.
The evaluator's implementation
view is private: single-state wrappers reject primed terms, while primed evaluation is
available only through a declaration-checked `CheckedBeforeAfter` whose before and
after environments are revalidated at the caller's fuel. Given-set atoms require an
explicit finite carrier observation in `ValueEnv`; nominal tags alone are rejected.
`ComponentValuation` binds strict inferred declarations, writable variables, and the
project event's effective deterministic actions before typed assignment; the refinement
adapters reuse this exact event source and variant-expression boundary, so fabricated
event names, cross-component variant pairs, and altered right-hand sides fail closed.
It is not evidence that
generated INV/GRD/SIM/WFIS/VAR obligations are semantically sound for an arbitrary
model; those require model-specific bindings to `EventB.Semantics`.

## Acceptance commands

Run these from a clean checkout with no private artifacts staged:

```sh
lake build EventB EventBWidgets Examples VariantFixtures gates rossi-dump eventb bench
lake env lean EventB/POGSoundness.lean
lake build EventB.POG.EQLAdapter
lake env lean EventB/POG/RefinementAdapters.lean
lake env lean test/EqlFixtures.lean
lake env lean test/GuardFixtures.lean
lake env lean test/EnabledGuardFixtures.lean
lake env lean test/FiniteSetEvaluatorFixtures.lean
lake env lean test/FiniteVariantFixtures.lean
lake env lean test/VwdFixtures.lean
lake env lean test/MrgFixtures.lean
lake env lean test/MrgSemanticFixtures.lean
lake env lean test/MrgAdapterFixtures.lean
lake env lean test/AdapterAxiomAudit.lean
lake exe gates --status
lake exe gates
pre-commit run --all-files
python3 tools/cli-fixtures.py
python3 tools/rossi-diff.py
python3 tools/distribution-check.py
python3 tools/manifest.py --check
git diff --check
```

The Rossi command requires the pinned official Rossi executable. CI downloads
`v0.1.7`, verifies SHA256
`698214d8082e2c9e0e8b638cd561ff0b6d9f1066ee5b79444f7ac54acfb7d10d`, and runs the
complete fixture matrix. The local command may instead use
`ROSSI_BIN=/path/to/rossi python3 tools/rossi-diff.py`.

On 2026-08-15, the pinned archive was executed as `rossi 0.1.7` in the disposable
x86_64 Linux QEMU/Lima guest. Its JSON validator returned success for all checked-in
fixtures: `actions.eventb` (1 component), `boundaries.eventb` (2), `identifiers.eventb`
(2), and `witnesses.eventb` (3); the combined `tools/rossi-diff.py` wrapper also passed.

The final manual release gate opens `examples/WidgetDemo.lean` and `examples/LspDemo.lean`
in VS Code with a restarted Lean server. On 2026-08-15 it was rerun successfully for
the current worktree: the WidgetDemo POG panel showed 11 derived obligations,
`external-declared: 11`, and `open / unproved: 0`; `#eventb_lsp_checks` passed; and the
native reference-location fix made Go to Definition from `sees LspContext` find the
declaration. A temporary unknown identifier produced the expected Lean diagnostic and
was discarded without saving. Terminal builds still cannot certify the Infoview's browser
layout.

## Known ceilings

- The pinned `.bpo` corpus omits the 200 P3b compatibility records described above.
- The corpus-scale P4 baseline has 73 external-declared results and 1060 unproved
  obligations; semantic bindings are required before claiming corpus-scale kernel proof.
- The bounded valuation adapter intentionally does not yet support partial/theory
  applications, binders/comprehensions, or automatic conversion of every generated POG
  formula into a model-specific semantic contract. Source-indexed INV/GRD/SIM/FIS
  fixtures and exact WFIS/WWD/integer-NAT-VAR/VWD witnesses are checked end-to-end;
  MRG target labels plus a checked two-branch source-indexed adapter, bounded integer
  EQL, EQL/FIN locator controls, and model-derived finite-set VAR are checked. Full
  abstract-event MRG provenance remains an explicit follow-up. Typed `ℙ(T)` evaluation
  and enabled guard fixtures are now covered. Source-bound parameterized enabledness,
  finite-domain witness evaluation, and well-founded variant contracts are accepted for
  their explicit supported slice; `ℙ1`, unbounded binders/comprehensions, partial/theory
  applications, and automatic semantic interpretation of arbitrary formulas remain
  outside the accepted subset.
  Refinement adapters now require explicit `FormulaAdequacy` witnesses that connect
  validity of the exact generated sequent to the corresponding semantic contract;
  these witnesses are still project-specific rather than inferred from names. These
  are explicit follow-up work rather than inferred semantics.
- Generality still has an explicit ceiling: `EventB.Semantics` now exposes and checks
  frame, gluing, merge, witness, parameterized-event, and well-founded-variant contracts,
  while `EventB.POGSoundness` exposes explicit translated-sequent validity. Generated POG
  classes are not all automatically bound to model-specific interpretations and operator
  soundness lemmas. Strict parameter scope, data-refinement glue after-state retention,
  right-oriented witnesses, and basic multi-event MRG have focused checked fixtures.
- `POG.generate`/`generateIn` remain compatibility APIs for the pinned corpus; trusted
  front ends must use `generateChecked`/`generateCheckedIn` and fail on diagnostics.
- Rodin `.bps` status names are not component-scoped; the provenance model/BPO source
  binding supplies that scope, while cryptographic authenticity remains outside this
  contract.
- XML roots without a name are accepted only when the caller supplies explicit component
  identity; this compatibility path is not an XML-authenticated identity proof.
- The official Rossi differential executable is provisioned in CI, not vendored.
- Raw Rossi/XML source navigation and visual ProofWidgets acceptance require the manual
  editor gate.
