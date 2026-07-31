# eventb-lean

An Event-B toolchain in Lean 4 with no Rodin in the pipeline. It reads Rodin's model
files, re-implements the static checker and the proof-obligation generator, and states
obligations against a refinement semantics whose soundness is a theorem rather than a
10,000-line Java program you have to trust.

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

## The point

Rodin cannot tell you which of your proofs rest on what. This can: `STATUS.md` carries a
trust ledger splitting every obligation into kernel-checked, SMT-trusted,
external-prover-trusted, and unproved. For a certification argument that distinction is
the whole conversation.

`Proved.sound` and `Refines.sound` in `EventB/Semantics.lean` are axiom-free, and CI
fails if that ever stops being true.

## Layout

`AGENTS.md` is the working agreement, `PLAN.md` the phase plan with measured gates, and
`STATUS.md` is generated. Start with `AGENTS.md`.

Corpus: AMAN (hhu-stups) and ERTMS-HL3 (eventB-Soton), vendored and pinned by sha256 in
`corpus/MANIFEST.tsv`. Both are third-party; check their licences before publishing.
