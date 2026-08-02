#!/usr/bin/env python3
"""Reject private book inputs from tracked or staged release content."""

import subprocess
import sys


FORBIDDEN = ("docs/event-b.md/", "docs/event-b.md.zip")


def paths(*args: str) -> list[str]:
    result = subprocess.run(["git", *args], capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or "git query failed")
    return result.stdout.splitlines()


def forbidden(path: str) -> bool:
    return any(path == prefix.rstrip("/") or path.startswith(prefix)
               for prefix in FORBIDDEN)


def main() -> int:
    try:
        candidates = paths("ls-files") + paths("diff", "--cached", "--name-only")
    except RuntimeError as error:
        print(f"distribution check: {error}", file=sys.stderr)
        return 1
    found = sorted(set(path for path in candidates if forbidden(path)))
    if found:
        print("private book artifacts must not be tracked or staged:", file=sys.stderr)
        print("\n".join(found), file=sys.stderr)
        return 1
    print("OK: private book artifacts are outside the release set")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
