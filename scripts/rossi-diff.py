#!/usr/bin/env python3
"""Compare the Rossi parser with EventB.Rossi on the checked-in matrix."""

import argparse
import json
import os
import shutil
import subprocess
from pathlib import Path


MATRIX = {
    "boundaries.eventb": [("Context", "boundary_ctx"),
                           ("Machine", "boundary_machine")],
    "identifiers.eventb": [("Context", "names_ctx"),
                            ("Machine", "names-machine")],
    "actions.eventb": [("Machine", "actions")],
}


def run(command):
    return subprocess.run(command, capture_output=True, text=True)


def official(rossi, fixture):
    result = run([rossi, "validate", "--format", "json",
                  "--continue-on-error", str(fixture)])
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip())
    rows = json.loads(result.stdout)
    if any(not row.get("success", False) for row in rows):
        raise RuntimeError(json.dumps(rows, sort_keys=True))
    return [(row["component_type"], row["component_name"]) for row in rows]


def ours(lake, fixture):
    result = run([lake, "exe", "rossi-dump", str(fixture)])
    rows = [json.loads(line) for line in result.stdout.splitlines()
            if line.startswith("{")]
    if result.returncode != 0 or len(rows) != 1 or not rows[0].get("success", False):
        raise RuntimeError(result.stderr.strip() or result.stdout.strip())
    return [(item["component_type"], item["component_name"])
            for item in rows[0]["components"]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rossi", default=os.environ.get("ROSSI_BIN") or
                        shutil.which("rossi"))
    parser.add_argument("--lake", default=os.environ.get("LAKE", "lake"))
    parser.add_argument("--fixtures", type=Path,
                        default=Path("test/rossi-fixtures"))
    args = parser.parse_args()
    if not args.rossi:
        parser.error("--rossi or ROSSI_BIN is required")

    failed = False
    for name, expected in MATRIX.items():
        fixture = args.fixtures / name
        try:
            left = official(args.rossi, fixture)
            right = ours(args.lake, fixture)
            if left != expected or right != expected:
                raise RuntimeError(f"expected {expected}, Rossi={left}, ours={right}")
            print(f"PASS {name}: {', '.join(f'{kind} {component}' for kind, component in left)}")
        except (OSError, RuntimeError, KeyError, json.JSONDecodeError) as error:
            failed = True
            print(f"FAIL {name}: {error}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
