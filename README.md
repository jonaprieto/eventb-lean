# eventb-lean

[![CI](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/eventb-lean?display_name=tag&sort=semver)](https://github.com/jonaprieto/eventb-lean/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.0-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/eventb-lean/)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Event-B models, formulas, proof obligations, refinement semantics, and Rodin comparison tools in
Lean 4. The reader accepts Rossi `.eventb` files and Rodin `.tuf` theories; the native DSL provides
the same proof-obligation generator and checker.

## Status and review

These libraries are actively evolving and are developed with AI assistance and human review.
CI and machine-checked proofs provide useful evidence, but do not guarantee correctness,
soundness, portability, performance, or suitability for every use case. Validate behavior
and assumptions before relying on a release.

Reviewer feedback is welcome, especially on correctness, proofs, API design, usability,
portability, performance, documentation, and real-world use. Please use the
[issue tracker](https://github.com/jonaprieto/eventb-lean/issues) or open a PR with a
reproducible example and the expected behavior.

## Quick start

```sh
lake build
lake exe eventb --help
lake exe eventb check test/rossi-fixtures/witnesses.eventb
lake exe gates
```

A native model uses the Event-B commands directly:

```lean
eventb_machine M where
  variables sched
  invariant inv1 : sched ⊆ AIRPLANES
  event Add where
    any a
    guard grd1 : "a ∈ AIRPLANES ∖ sched"
    action act1 : sched := sched ∪ {a}

#eventb_pog M
```

The CLI reports parsed models, generated obligations, proof status, trust mode, formulas, and
fingerprints. `eventb diff` compares generated obligations with Rodin artifacts; `eventb report`
provides machine-readable output.

The current pinned-corpus snapshot is 38/38 reader, 1102/1102 formula, 940/940 typing,
1133/1133 obligation-name, 1132/1325 derived-statement, and 73/1133 external-declared
baseline checks. Remaining obligations stay visibly unproved; imported Rodin status is accepted
only after supplied-artifact POG regeneration and canonical BPO comparison.
`EventB.Semantics` provides proof-carrying invariant/refinement contracts, including
frame, gluing, merged-event, witness, and variant contracts. `EventB.POGSoundness`
provides explicit translated-sequent validity; formula interpretations remain
caller-supplied and are never guessed.

## Verification

```sh
lake build EventB Examples
lake exe gates
lake exe gates --status
```

The corpus gate is pinned by `corpus/MANIFEST.tsv`. The checked-in Rossi fixtures cover parser
boundaries and a typecheckable witness project. Optional ProofWidgets views are built with the
examples target.

For the manual editor gate, open `examples/WidgetDemo.lean` and `examples/LspDemo.lean` in VS
Code with the Lean server restarted. Confirm the Infoview model/PO sections, derived goals,
explicit trust badges, Go to Definition, and an unknown-identifier diagnostic; discard any
temporary diagnostic edit before closing the files.

## Related projects

[`lean-grip`](https://github.com/jonaprieto/lean-grip) supplies byte parsing;
[`lean-argus`](https://github.com/jonaprieto/lean-argus) supplies CLI parsing; and
[`termcolor-diagnostics`](https://github.com/jonaprieto/lean-termcolor-diagnostics) supplies
source-aware diagnostics.

## License

Apache-2.0.
