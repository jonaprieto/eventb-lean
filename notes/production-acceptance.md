# Production acceptance

This note is the release checklist for the first production-ready eventb-lean
commit. It describes the supported contract and the measured ceilings; it does not
claim that every proof obligation is automatically discharged.

## Measured baseline

The acceptance run uses Lean `v4.28.0`, the pinned corpus manifest
`84d51dbc09498d0b3c61d3a69a0d7aa700390983c53ef6dd5b8b26a9b61e4e2f`, `grip`
`eb29a2331729a7087eab54838557e7490e802a29`, and ProofWidgets `v0.0.87`.
The timestamped gate record in
`bench/results/2026-08-02T21-56-30Z/gates.txt` records the measured commit and
toolchain metadata.

| Gate | Result | Interpretation |
| --- | ---: | --- |
| P0 reader | 38/38 | Source files read losslessly. |
| P1 formulas | 1102/1102 | Formulas parse and round-trip. |
| P2 types | 940/940 | Recorded identifier types reproduced. |
| P3 obligations | 1133/1133 | Rodin PO names generated. |
| P3b statements | 1129/1322 | Derived goals match the comparable corpus records. |
| P3b hypotheses | 1129/1322 | Derived hypothesis sets match the comparable records. |
| P3b compatibility | 200 pinned | 193 no-sequent records plus 7 WFIS name-only records. |
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

## Acceptance commands

Run these from a clean checkout with no private artifacts staged:

```sh
lake build EventB EventBWidgets Examples gates rossi-dump eventb bench
lake exe gates
python3 scripts/cli-fixtures.py
python3 scripts/rossi-diff.py
python3 scripts/distribution-check.py
python3 scripts/manifest.py --check
python3 scripts/style-check.py
git diff --check
```

The Rossi command requires the pinned official Rossi executable. CI downloads
`v0.1.7`, verifies SHA256
`698214d8082e2c9e0e8b638cd561ff0b6d9f1066ee5b79444f7ac54acfb7d10d`, and runs the
complete fixture matrix. The local command may instead use
`ROSSI_BIN=/path/to/rossi python3 scripts/rossi-diff.py`.

The final manual release gate opens `examples/WidgetDemo.lean` and `examples/LspDemo.lean`
in VS Code with a restarted Lean server. It checks the widget panels, replayed entries,
Go to Definition, and unknown-symbol diagnostics. Terminal builds cannot certify the
Infoview's browser layout, so this gate must be recorded separately.

## Known ceilings

- The pinned `.bpo` corpus omits the 200 P3b compatibility records described above.
- The corpus-scale P4 baseline has 73 external-trusted results and 1060 unproved
  obligations; semantic bindings are required before claiming corpus-scale kernel proof.
- The official Rossi differential executable is provisioned in CI, not vendored.
- Raw Rossi/XML source navigation and visual ProofWidgets acceptance require the manual
  editor gate.
