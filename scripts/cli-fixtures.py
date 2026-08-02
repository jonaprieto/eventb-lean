#!/usr/bin/env python3
"""Exercise the shipped CLI against the checked-in compatibility fixtures."""

import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LAKE = os.environ.get("LAKE", "lake")
FIXTURES = ROOT / "test" / "rossi-fixtures"


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [LAKE, "exe", "eventb", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )


def expect(name: str, result: subprocess.CompletedProcess[str], code: int,
           stdout: str = "", stderr: str = "") -> None:
    if result.returncode != code:
        raise AssertionError(
            f"{name}: exit {result.returncode}, expected {code}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    if stdout and stdout not in result.stdout:
        raise AssertionError(f"{name}: stdout lacks {stdout!r}\n{result.stdout}")
    if stderr and stderr not in result.stderr:
        raise AssertionError(f"{name}: stderr lacks {stderr!r}\n{result.stderr}")


def json_lines(value: str) -> list[dict[str, object]]:
    return [json.loads(line) for line in value.splitlines() if line.strip()]


def check_witness() -> None:
    path = str(FIXTURES / "witnesses.eventb")
    result = run("check", path, "--json")
    expect("witness check", result, 0)
    records = json_lines(result.stdout)
    actual = [(record["machine"], record["name"], record["kind"],
               record["derived"], record["hypothesis_only"]) for record in records]
    expected = [
        ("Abstract", "step/inv/INV", "INV", True, False),
        ("Concrete", "step/inv/INV", "INV", True, False),
        ("Concrete", "step/grd/GRD", "GRD", True, False),
        ("Concrete", "step/act/SIM", "SIM", True, False),
        ("Concrete", "step/act/WD", "WD", True, False),
        ("Concrete", "step/wit/WFIS", "WFIS", True, False),
        ("Concrete", "step/wit/WWD", "WWD", False, True),
    ]
    if actual != expected:
        raise AssertionError(f"witness check: records differ\n{actual}")

    result = run("summary", path, "--json")
    expect("witness summary", result, 0)
    summary = json.loads(result.stdout)
    if summary != {
        "obligations": 7,
        "derived": 6,
        "by_class": {"INV": 2, "GRD": 1, "SIM": 1, "WD": 1, "WFIS": 1,
                      "WWD": 1},
        "not_derived": 1,
        "not_derived_by_class": {"WWD": 1},
        "hypothesis_only": 1,
        "by_machine": {
            "C": {"obligations": 0, "derived": 0},
            "Abstract": {"obligations": 1, "derived": 1},
            "Concrete": {"obligations": 6, "derived": 5},
        },
    }:
        raise AssertionError(f"witness summary: unexpected JSON\n{summary}")

    result = run("report", path)
    expect("witness report", result, 0)
    report = json.loads(result.stdout)
    if report["coverage_source"] != "none":
        raise AssertionError("witness report: Rossi-only coverage must be none")
    if len(report["obligations"]) != 7:
        raise AssertionError("witness report: expected seven obligations")
    if report["trust_ledger"] != {
        "kernel-checked": 0,
        "smt-trusted": 0,
        "rodin-imported": 0,
        "external-trusted": 2,
        "unproved": 5,
    }:
        raise AssertionError("witness report: trust ledger changed")

    result = run("po", path, "step/wit/WWD")
    expect("witness WWD", result, 0, "(no statement derived)")
    result = run("po", path, "step/wit/WFIS")
    expect("witness WFIS", result, 0, "∃")
    result = run("prove", path)
    expect("witness prove", result, 0, "local baseline: 2/7 discharged")


def check_rossi_dump() -> None:
    expected = {
        "actions.eventb": [("Machine", "actions")],
        "boundaries.eventb": [("Context", "boundary_ctx"),
                               ("Machine", "boundary_machine")],
        "identifiers.eventb": [("Context", "names_ctx"),
                                ("Machine", "names-machine")],
        "witnesses.eventb": [("Context", "C"), ("Machine", "Abstract"),
                              ("Machine", "Concrete")],
    }
    for name, components in expected.items():
        result = run("check", str(FIXTURES / name), "--json")
        if name == "actions.eventb":
            expect("actions semantic boundary", result, 1,
                   stderr="not a predicate operator")
        elif name == "boundaries.eventb":
            expect("boundaries semantic boundary", result, 1,
                   stderr="cannot unify S with ℤ")
        elif name == "identifiers.eventb":
            expect("identifiers check", result, 0)
        else:
            expect("witness semantic check", result, 0)

        result = subprocess.run(
            [LAKE, "exe", "rossi-dump", str(FIXTURES / name)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        expect(f"rossi-dump {name}", result, 0)
        rows = json_lines(result.stdout)
        actual = [(item["component_type"], item["component_name"])
                  for item in rows[0]["components"]]
        if actual != components:
            raise AssertionError(f"rossi-dump {name}: components differ")


def check_theories_and_errors() -> None:
    result = run("theory", "test/fixtures/theories")
    expect("theory directory", result, 0, "Derived: 1 symbols")
    if "Base: 1 symbols" not in result.stdout:
        raise AssertionError("theory directory: missing Base summary")
    result = run("theory", "test/fixtures/theories/a-derived.tuf")
    expect("theory missing dependency", result, 1, stderr="Base` is not registered")

    result = run("check", str(FIXTURES / "witnesses.eventb"), "--kind", "BAD")
    expect("unknown kind", result, 1, stderr="unknown obligation class")
    result = run("check", str(FIXTURES / "witnesses.eventb"), "--machine", "Missing")
    expect("missing machine", result, 1, stderr="no component named Missing")

    result = run("diff", "test/fixtures/theories")
    expect("diff missing Rodin sources", result, 1, stderr="contains no .bum or .buc")


def check_corpus_diff() -> None:
    result = run("diff", "corpus/aman")
    expect("corpus diff", result, 0, stdout="M0_AMAN_Update")


def main() -> int:
    checks = [check_witness, check_rossi_dump, check_theories_and_errors,
              check_corpus_diff]
    try:
        for check in checks:
            check()
            print(f"PASS {check.__name__}")
    except (AssertionError, json.JSONDecodeError, IndexError, KeyError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
