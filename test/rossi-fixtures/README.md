# Rossi fixture contract

These fixtures are split by purpose. `tools/cli-fixtures.py` is the executable
expectation file; it checks both output and exit status.

| Fixture | Purpose | `eventb check` |
| --- | --- | --- |
| `actions.eventb` | Wrapped and adjacent action parsing | Expected typechecking failure: the model has no typing context. |
| `boundaries.eventb` | Multiline formulas and action boundaries | Expected typechecking failure: `v + y` is invalid for values in `S`. |
| `identifiers.eventb` | Component names and reserved-word boundaries | Passes with zero generated obligations. |
| `witnesses.eventb` | End-to-end refinement, witness, WFIS, and WWD behavior | Passes with thirteen obligations. |

All four fixtures must pass `rossi-dump` with their expected component names. The
two parser-boundary fixtures are not valid semantic projects; their nonzero checker
status is part of the test contract, not a parser failure.

Run the complete fixture contract from the repository root:

```sh
python3 tools/cli-fixtures.py
```
