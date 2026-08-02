# eventb-lean

An Event-B toolchain in Lean 4 with no Rodin in the pipeline. It reads Rodin's model
files, re-implements the static checker and the proof-obligation generator, and states
obligations against a refinement semantics whose soundness is a theorem rather than a
10,000-line Java program you have to trust.

See [the architecture note](notes/architecture.md) for the layers, native theory
scope, trust boundary, and verification contract.

[![CI](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/eventb-lean/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![reader](https://img.shields.io/badge/reader-38%2F38-brightgreen)](baseline/parse.tsv)
[![formulas](https://img.shields.io/badge/formulas-1102%2F1102-brightgreen)](baseline/formula.tsv)
[![types](https://img.shields.io/badge/types-940%2F940-brightgreen)](baseline/typecheck.tsv)
[![obligations](https://img.shields.io/badge/obligations-1133%2F1133-brightgreen)](baseline/pog.tsv)
[![statements](https://img.shields.io/badge/statements-1129%2F1322-yellow)](baseline/statement.tsv)
[![hypotheses](https://img.shields.io/badge/hypotheses-1129%2F1322-yellow)](baseline/hypothesis.tsv)
[![compatibility](https://img.shields.io/badge/compatibility-200%20pinned-yellow)](baseline/compatibility.tsv)

```
$ lake exe gates
P0 reader: 38/38
P1 formulas: 1102/1102
P2 types: 940/940
P3 obligations: 1133/1133
P3b statements: 1129/1322 derived
P3b hypotheses: 1129/1322 derived
P3b compatibility: 200 pinned omissions
P4 local baseline: 73/1133 discharged
```

P0 through P3 are exact against the pinned corpus. P3b derives 1129 of 1322 comparable
goals and hypotheses; its 200 compatibility records are explicit data: 193 generated
targets have no matching sequent in the pinned `.bpo` files, plus seven WFIS names that
Rodin records without a target predicate. P4 currently has 73 external-trusted local
results and 1060 unproved obligations; no corpus obligation is classified as
kernel-checked, SMT-trusted, or imported from Rodin.

## Using it

From a checkout, this verifies the library, widgets, every executable example and
tool, the corpus ratchet, and the repository style:

```sh
$ lake build
$ lake build EventBWidgets Examples gates rossi-dump eventb bench
$ lake exe gates
$ python3 scripts/style-check.py
$ python3 scripts/cli-fixtures.py
$ python3 scripts/distribution-check.py
$ python3 scripts/manifest.py --check
$ git diff --check
```

The GitHub workflow builds `EventB`, `EventBWidgets`, `Examples`, `gates`, `rossi-dump`,
`eventb`, and `bench`. It also runs the CLI fixture matrix, pinned Rossi differential
matrix, style, manifest, distribution, gate, and soundness checks. The exact release
record is maintained in [the production acceptance note](notes/production-acceptance.md).

## Supported input contract

All supported authoring paths lower into the same model, typing, and proof-obligation
pipeline. “Supported” means that unsupported syntax is rejected with a diagnostic; it
does not mean that every generated obligation is automatically proved.

| Input | Supported role | Boundary |
| --- | --- | --- |
| Rodin `.bum` / `.buc` | Read source machines and contexts | The pinned corpus is the compatibility oracle; unsupported XML extensions are diagnosed. |
| Rodin `.bpo` / `.bps` | Compare PO names, types, sequents, and recorded status | They are comparison/trust inputs, not a replacement for native typing or proof. |
| Rossi `.eventb` | Read supported Rossi text projects, including components, labels, witnesses, refinements, variants, and statuses | The supported grammar subset is explicit; malformed or unsupported structure fails with a source diagnostic. |
| Native Lean DSL | Author contexts, machines, theories, datatypes, definitions, and rules | Concrete formula translation needs explicit Lean semantic bindings. |
| Rodin `.tuf` | Import/export the faithful theory subset with symbols, imports, datatypes, definitions, and rules | Unknown extensions and declarations without a faithful native representation are rejected. |

The CLI loads a `.eventb` file directly or a project directory containing Rossi/Rodin
source files. Theory directories are loaded in dependency order; a single theory file
that imports an unprovided theory fails rather than inventing a dependency. Raw
Rossi/XML source ranges are not currently promised for editor navigation.

Build the executable, then point it at a Rodin project directory. `check` lists the
generated obligations; `diff` compares their names with Rodin's `.bpo` files:

```text
$ lake exe eventb check corpus/aman --machine M0_AMAN_Update --kind INV
M0_AMAN_Update: INITIALISATION/inv0,1/INV [INV] derived
M0_AMAN_Update: AMAN_Update/inv0,1/INV [INV] derived

$ lake exe eventb diff corpus/aman | head -n 6
M0_AMAN_Update: 0 match, 0 only Rodin, 2 only ours
  only ours: INITIALISATION/inv0,1/INV, AMAN_Update/inv0,1/INV
M0_AMAN_Update_Ctx: 0 match, 0 only Rodin, 0 only ours
M0_AMAN_Update_prob_mc_Ctx: 1 match, 0 only Rodin, 0 only ours
M1_Landing_Sequence: 13 match, 0 only Rodin, 8 only ours
  only ours: INITIALISATION/inv13,2/WD, INITIALISATION/act0,1/SIM, AMAN_Update/inv13,2/WD, AMAN_Update/grd0,1/GRD, AMAN_Update/act0,1/SIM, AMAN_Update/newScheduledAirplanes/WFIS, Move_Aircraft/inv13,2/WD, Move_Aircraft/act1,1/WD
```

The project loader also accepts Rossi `.eventb` files and Rodin `.tuf` theories:

```text
$ lake exe eventb theory path/to/theories
$ lake exe eventb prove path/to/project
$ lake exe eventb report path/to/project > report.json
```

`report` is the machine-readable handoff for automation: each obligation includes its
P3 name-coverage status (when `.bpo` files are present), derived status, proof rule,
trust mode, formula, fingerprint, and translation diagnostic. It never labels an
unbound model as kernel-checked.

The checked-in Rossi fixtures under `test/rossi-fixtures/` cover parser boundaries and
one fully typecheckable witness project. The parser-boundary fixtures are not all
semantically valid Event-B models, so `rossi-dump` is the appropriate structural test
for them; use `eventb check` and `eventb report` for `witnesses.eventb`.

## Manual editor acceptance

The ProofWidgets surface needs one editor check in addition to the terminal contract:

1. Run `lake build EventB EventBWidgets Examples` from a clean checkout.
2. Open `examples/WidgetDemo.lean` in VS Code with the Lean extension and restart the
   Lean server.
3. Confirm the Infoview shows `Event-B proof obligations · BridgeController`, model
   panels, obligation class sections, hypotheses, goals, trust badges, fingerprints,
   and the 11 replayed entries. There must be no React error, `Click to reload`, or
   `No info found` result for the widget commands.
4. Open `examples/LspDemo.lean`; use Go to Definition on `LIMIT`, `cars`, `step`, and
   `inv`. The native declaration-range checks in that file must also compile.
5. Introduce an unknown identifier in a native formula temporarily and confirm the
   editor reports `unknown Event-B identifier`; revert the temporary edit.

This is a release gate, not a claim that terminal compilation verifies browser layout.
The acceptance note records whether this manual check has been performed.

Do not commit screenshots, editor state, or the private book export. Native DSL
declarations have Lean source ranges; raw Rossi/XML inputs currently expose parser
diagnostics but do not promise source navigation ranges.

## Why the numbers mean something

There are no hand-written answers in the corpus gate. Rodin already wrote its answers
into the model files, so the corpus labels itself:

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
  invariant inv1 : sched ⊆ AIRPLANES
  event Add where
    any a
    guard grd1 : "a ∈ AIRPLANES ∖ sched"
    action act1 : sched := sched ∪ {a}

#eventb_pog M Ctx
-- Add/inv1/INV
--     ⊢ ((sched ∪ {a}) ⊆ AIRPLANES)
```

Predicates use ordinary Lean term syntax where the notation is compatible; quoted
formulas remain available for Event-B-only operators such as `∖`. Actions use `:=` as
the unquoted spelling of Event-B's `≔`. A formula that is not Event-B is an elaboration
error pointing at the formula. See `examples/Counter.lean`.

The DSL also checks names against the component environment: context symbols, machine
variables and event parameters (including primed after-state variables) are the only
user identifiers visible in a formula. A misspelling such as `LIMITT` is therefore an
elaboration error instead of an unresolved model symbol.

The executable examples are ordinary Lean sources. The core model files are the
introductory `Counter.lean` and the three book-derived files `BookBridge.lean`,
`BookPrograms.lean`, and `BookSystems.lean`; the remaining files cover widgets, theories,
translation, trust, Rossi input, LSP ranges, and the local prover. Together they contain
20 contexts and 43 machines. `lake build Examples` checks them through the same DSL,
typechecker, and proof-obligation generator as Rodin files.

The book export also contains proof trees, pseudocode, OCR fragments, and image-only
blocks. Those are documentation, not executable Event-B inputs; the four book-derived
files cover the model examples that can be represented and checked by this toolchain.

The repository contains 15 executable example modules and 8 focused test/fixture
entries. The examples use compile-time `#guard` checks and elaborator commands; the
corpus gates provide the independent large-scale comparison against Rodin artifacts.

## Infoview proof obligations

For an interactive view in the Lean VS Code Infoview, open
`examples/WidgetDemo.lean`. It uses the optional ProofWidgets front end:

```lean
#eventb_model_widget widgetProject WidgetCtx
#eventb_model_widget widgetProject BridgeController
#eventb_pog_widget_with_ledger widgetProject BridgeController widgetLedger
#eventb_pog_widget_in theoryEnv theoryProject TheoryMachine
```

The first panels show the context and machine surface—symbols, axioms, invariants,
events, and refinement links. The last panel shows obligation counts, classes,
hypotheses, generated goals, and replayed evidence in expandable cards. The demo passes
its ledger explicitly and replays all 11 obligations against Lean declarations during
build. `lake build Examples` compiles this demo; widgets do not alter the CLI, POG
output, proof status, or trust ledger.

For explicit semantic contexts, `EventB.Theory.Embed` checks definitions and datatype
constructors, while `EventB.Trust.Replay.translateStatement` translates a complete
goal-plus-hypotheses sequent without assigning trust. A `kernel` entry is assigned only
after the corresponding Lean proof is replayed and its axiom metadata matches.

Unquoted identifiers in DSL formulas also support native Go to Definition: clicking
`LIMIT` in `cars < LIMIT` jumps to `constants LIMIT`. Quoted formulas remain available
for Event-B operators that Lean syntax cannot represent, but do not provide identifier
navigation.


At the PO-name level, `eventb diff` reports **1133 obligations matching Rodin, none only
Rodin has, and 649 only we have**. The additional obligations are explicit generated
coverage, mostly well-definedness conditions Rodin does not serialize. This is a
name-level result; the stricter goal-and-hypothesis comparison is the P3b result shown
above. A spurious obligation costs proof effort, while a missing obligation would be
unsound.

## The point

Rodin cannot tell you which of your proofs rest on what. This can: `lake exe gates
--status` writes a trust ledger splitting every obligation into kernel-checked,
SMT-trusted, Rodin-imported, external-prover-trusted, and unproved. The current local
baseline records 73 external-trusted results; it does not claim they are kernel proofs.

`Proved.sound` and `Refines.sound` in `EventB/Semantics.lean` are axiom-free, and CI
fails if that ever stops being true.

## Layout

`EventB/` is the library, `test/Gates.lean` the ratchet that measures it against the
corpus, and `baseline/*.tsv` the per-item record it diffs against. Architecture notes
live in `notes/`; `STATUS.md` is generated by the gates.

Corpus: AMAN (hhu-stups) and ERTMS-HL3 (eventB-Soton), vendored and pinned by sha256 in
`corpus/MANIFEST.tsv`. Both are third-party; check their licences before publishing.
