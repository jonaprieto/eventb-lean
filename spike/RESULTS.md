# P4 discharge spike

Question: can Lean's automation discharge Event-B proof obligations at a rate
comparable to Rodin's provers? Answered before building a POG that emits statements,
because a bad answer would mean building a B prover first, which is a different and much
larger project.

Rodin's bar, from the `.bps` files: **all 1133 obligations discharged, 1088 of them
automatically.**

## Result

```
1133  obligations extracted from the corpus (hypotheses + goal, fully resolved)
1133  translated into Lean over spike/Spike/Prelude.lean          100%
1110  closed by bare `grind`                                       98.0%
1053  closed by bare `grind` with the hypotheses REMOVED           92.9%
```

The second number is the one that matters. **Most of this corpus is trivial.** 1053 of
1133 obligations are provable with no hypotheses at all: they are `∅ ⊆ X`,
`dom r = dom r`, and similar, because Event-B's generator emits an obligation for every
event against every invariant it can touch, and INITIALISATION sets most variables to
`∅`. Rodin's provers close them instantly too, which is why its automatic rate is 1088.

So the honest figure is the informative subset, the 80 obligations whose hypotheses
actually do work:

```
  80  need their hypotheses
  62  closed once given them            78%
  18  still fail
```

**78% on the obligations that are not tautologies.** That is the number that predicts
effort on a real development, and it is a good number: it says existing Lean automation
is a viable backend, not that Event-B is easy.

Of the 23 remaining failures, exactly **one** is a `grind` failure. The other 22 are
elaboration errors in the translator, mostly application type mismatches.

## Why the numbers can be trusted

Three controls, because a 98% rate against an incumbent's 96% deserves suspicion rather
than a victory lap:

- **Negative control.** A false statement of the same shape (`x ∈ dom r` for arbitrary
  `r`, `x`) makes `grind` fail; a true one of the same shape succeeds.
- **Hypothesis-removal control.** Re-running with every hypothesis dropped is what
  exposed the triviality above. Without it this document would have claimed 98%.
- **A specific false goal.** `Set.Finite (Set.univ : Set AIRPLANES)` holds in Event-B
  only because the context states `finite(AIRPLANES)` as an axiom; for an arbitrary Lean
  type it is false. `grind` correctly refuses it, and the scorer records it as failing.

Two measurement bugs were found and fixed along the way, both of which inflated results:

- The extractor used a regex, and regexes mis-pair nested `poPredicateSet` elements, so
  961 of 1133 sequents reached Lean with no hypotheses at all. Rodin keeps a sequent's
  hypotheses in a parent chain of predicate sets; the extractor now walks it with a real
  XML parse. Identifiers went from 172 to 1049.
- The scorer compared Lean's error lines against `theorem` declaration lines. Lean
  reports an error at the failing *tactic* line, so the two never matched and every
  theorem counted as passing. `score.py` now attributes each error to the enclosing
  declaration.

## Layout

- `extract.py` resolves each sequent's hypotheses and identifiers from the `.bpo`.
- `Spike/Prelude.lean` is Event-B set theory over Mathlib's `Set`: relations as sets of
  pairs, the arrow families as sets of relations, `max`/`min`/`app` as definite
  descriptions pinned down only where their well-definedness condition holds. A real POG
  would emit into exactly this.
- `translate.py`, `build.py` turn obligations into Lean theorems; `build.py --no-hyps`
  runs the control. Deliberately throwaway: the production translator belongs in the
  POG, emitting terms rather than text.
- `score.py` attributes failures to theorems. `measure.sh <tactic> [n]` drives it.

Mathlib is required, so the spike is a separate lake project and the main library's
dependency closure stays batteries-only.

## What this justifies

Building the real thing: `Obligation` carrying a statement rather than just a name,
elaborated against `EventB/Semantics.lean`. The spike says the goals that come out the
far end are within reach of existing automation, and that the corpus needed to *measure*
future progress is the 80, not the 1133.
