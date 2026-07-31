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
 499  translated into Lean over spike/Spike/Prelude.lean
 477  closed by bare `grind`                       95.6% of those attempted
   0  `grind` failures
```

Every one of the 22 misses is a translation or elaboration gap, not an unproved goal.
`grind` did not fail on a single well-formed obligation.

**Lean's automation is not the bottleneck. Faithful translation is.** That is the
opposite of what this project assumed at the outset, and it is the reason to keep going.

## What the number does not say

The 499 are not a random sample. They are what a quick translator could express, so they
skew toward the simpler obligations. The 634 not translated need `max`/`min` over sets
(226), lambda and set-comprehension binders, `partition`, and relational override in
positions the translator does not yet cover. Those are plausibly harder to discharge as
well as harder to state, so the true rate over all 1133 lies somewhere between 42% (if
every untranslated obligation fails) and about 96%.

Verified by negative control, not by the number alone: a false statement in the same
shape (`x ∈ dom r` for arbitrary `r`, `x`) makes `grind` fail, and a true one in the same
shape succeeds. An earlier run reporting 51% was measuring a broken extractor: a regex
mis-paired nested `poPredicateSet` elements, so 961 of 1133 sequents were handed to Lean
with no hypotheses at all.

## Layout

- `extract.py` resolves each sequent's hypotheses by walking the parent chain of
  predicate sets, which is where Rodin keeps them. Real XML parse; a regex gets it wrong.
- `Spike/Prelude.lean` is Event-B set theory over Mathlib's `Set`: relations as sets of
  pairs, the arrow families as sets of relations, and application as a definite
  description that is only pinned down where the well-definedness hypothesis holds. A
  real POG would emit into exactly this.
- `translate.py` and `build.py` turn obligations into Lean theorems. Deliberately
  throwaway: the spike is a measurement, and the production translator belongs in the
  POG emitting terms rather than text.
- `measure.sh <tactic> [n]` runs it.

Mathlib is required, so the spike is a separate lake project and the main library's
dependency closure stays batteries-only.

## What this justifies

Building the real thing: `Obligation` carrying a statement rather than just a name,
elaborated against `EventB/Semantics.lean`. The spike says the goals that come out the
far end are within reach of existing automation.
