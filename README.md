# eventb

[![CI](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/eventb-lean?display_name=tag&sort=semver)](https://github.com/jonaprieto/eventb-lean/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.0-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/eventb-lean/)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Event-B models, formulas, proof obligations, refinement semantics, and Rodin comparison tools in
Lean 4. The reader accepts Rossi `.eventb` files and Rodin `.tuf` theories; the native DSL provides
the same proof-obligation generator and checker.

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

## Verification

```sh
lake build EventB EventB.Properties Examples
lake exe gates
lake exe gates --status
```

The corpus gate is pinned by `corpus/MANIFEST.tsv`. The checked-in Rossi fixtures cover parser
boundaries and a typecheckable witness project. Optional ProofWidgets views are built with the
examples target.

## Related projects

[`oatp`](https://github.com/jonaprieto/oatp) supplies ATP orchestration and
[`lean-grip`](https://github.com/jonaprieto/lean-grip) supplies byte parsing.

## License

Apache-2.0.
