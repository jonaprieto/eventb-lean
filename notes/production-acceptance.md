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
| P4 local baseline | 73/1133 | Explicit external-trusted evidence; 1060 remain unproved. |

The P3b compatibility records are not silently omitted or counted as proof failures.
They are pinned, classified, regression-tested, and reported by the gates. The P4
count is a measured baseline, not a percentage claim. Kernel, SMT, and imported-Rodin
counts are zero for the corpus baseline; the local results remain external-trusted.

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
  documented compatibility projection for pinned Rodin omissions.
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
Rodin imports additionally require model-root identity, source-component binding, the
named BPO sequent, and equality of its canonical goal and hypothesis multiset with the
generated obligation, plus an independently parsed proof-status record. Re-deriving
the POG from model bytes remains outside this contract; the current digest primitive is
an internal fingerprint, not a cryptographic authenticity claim. Legacy status-only
Rodin evidence is rejected; model, BPO, and status provenance are mandatory. SMT and
external verifier fields remain caller-supplied metadata and are never presented as
Lean-kernel replay.

## Acceptance commands

Run these from a clean checkout with no private artifacts staged:

```sh
lake build EventB EventBWidgets Examples gates rossi-dump eventb bench
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

On 2026-08-14, the pinned archive was also executed as `rossi 0.1.7` in a
disposable x86_64 Linux QEMU/Lima guest. Its JSON validator returned success for
all checked-in fixtures: `actions.eventb` (1 component), `boundaries.eventb`
(2), `identifiers.eventb` (2), and `witnesses.eventb` (3). The exact combined
`tools/rossi-diff.py` command remains a CI gate because the local Lean executable
is host-native while the pinned Rossi artifact is Linux x86_64.

The final manual release gate opens `examples/WidgetDemo.lean` and `examples/LspDemo.lean`
in VS Code with a restarted Lean server. It checks the widget panels, replayed entries,
Go to Definition, and unknown-symbol diagnostics. Terminal builds cannot certify the
Infoview's browser layout, so this gate must be recorded separately.

## Known ceilings

- The pinned `.bpo` corpus omits the 200 P3b compatibility records described above.
- The corpus-scale P4 baseline has 73 external-trusted results and 1060 unproved
  obligations; semantic bindings are required before claiming corpus-scale kernel proof.
- Generality still has an explicit ceiling: full frame/gluing-relation semantics and
  semantic soundness proofs for every generated PO class remain follow-up work. Strict
  parameter scope, data-refinement glue after-state retention, right-oriented witnesses,
  and basic multi-event MRG have focused checked fixtures.
- `POG.generate`/`generateIn` remain compatibility APIs for the pinned corpus; trusted
  front ends must use `generateChecked`/`generateCheckedIn` and fail on diagnostics.
- Rodin `.bps` status names are not component-scoped; the provenance model/BPO source
  binding supplies that scope, while cryptographic authenticity remains outside this
  contract.
- The official Rossi differential executable is provisioned in CI, not vendored.
- Raw Rossi/XML source navigation and visual ProofWidgets acceptance require the manual
  editor gate.
