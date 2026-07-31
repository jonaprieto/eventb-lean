# eventb-lean

An Event-B toolchain in Lean 4 with no Rodin in the pipeline. It reads Rodin's model
files, re-implements the static checker and the proof-obligation generator, and states
obligations against a refinement semantics whose soundness is a theorem rather than a
10,000-line Java program you have to trust.

[![CI](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![reader](https://img.shields.io/badge/reader-38%2F38-brightgreen)](baseline/parse.tsv)
[![formulas](https://img.shields.io/badge/formulas-1102%2F1102-brightgreen)](baseline/formula.tsv)
[![types](https://img.shields.io/badge/types-940%2F940-brightgreen)](baseline/typecheck.tsv)
[![obligations](https://img.shields.io/badge/obligations-1105%2F1133-yellow)](baseline/pog.tsv)
[![statements](https://img.shields.io/badge/statements-856%2F1033-yellow)](baseline/statement.tsv)

```
$ lake exe gates
P0 reader: 38/38
P1 formulas: 1102/1102
P2 types: 940/940
P3 obligations: 1105/1133
```

## Why the numbers mean something

There are no hand-written fixtures. Rodin already wrote its answers into the model
files, so the corpus labels itself:

| File | Holds | Checks |
|---|---|---|
| `.bum` / `.buc` | the model | the reader and the formula parser |
| `.bpo` | obligations, **with every inferred type** | the typechecker and the POG |
| `.bps` | per-obligation proof status | the discharge rate |

Nothing in a `.bum` states a type. Matching the 940 in the `.bpo` means reproducing the
derivation, not reading an answer off the file.

## Two front ends

Read Rodin's files, or write Event-B directly in Lean. Both elaborate to the same tree,
so the typechecker, the generator and every gate are shared:

```lean
eventb_machine M where
  sees Ctx
  variables sched
  invariant inv1 : "sched ⊆ AIRPLANES"
  event Add where
    any a
    guard grd1 : "a ∈ AIRPLANES ∖ sched"
    action act1 : "sched ≔ sched ∪ {a}"

#eventb_pog M Ctx
-- Add/inv1/INV
--     ⊢ ((sched ∪ {a}) ⊆ AIRPLANES)
```

A formula that is not Event-B is a Lean elaboration error pointing at the literal. See
`examples/Counter.lean`.

## The point

Rodin cannot tell you which of your proofs rest on what. This can: `lake exe gates
--status` writes a trust ledger splitting every obligation into kernel-checked,
SMT-trusted, external-prover-trusted, and unproved. For a certification argument that
distinction is the whole conversation.

`Proved.sound` and `Refines.sound` in `EventB/Semantics.lean` are axiom-free, and CI
fails if that ever stops being true.

## Layout

`EventB/` is the library, `test/Gates.lean` the ratchet that measures it against the
corpus, and `baseline/*.tsv` the per-item record it diffs against. Working notes and the
generated status report are kept out of the repo.

Corpus: AMAN (hhu-stups) and ERTMS-HL3 (eventB-Soton), vendored and pinned by sha256 in
`corpus/MANIFEST.tsv`. Both are third-party; check their licences before publishing.
