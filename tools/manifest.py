#!/usr/bin/env python3
"""Regenerate corpus/MANIFEST.tsv and print the gate denominators.

The manifest pins every vendored corpus file by size and sha256, and records the
upstream repo and commit it came from. Every number in baseline/ is meaningless
without it: a silently changed corpus turns a passing ratchet into a lie.

    python3 tools/manifest.py            # rewrite manifest, print gate counts
    python3 tools/manifest.py --check    # verify only, exit 1 on drift
"""

import collections
import glob
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ORIGINS = {
    "aman": "https://github.com/hhu-stups/AMAN-abstraction-example"
    "@1376af673eab5f96c0408328ba76dde2e07b65e4 Abstraction/",
    "ertms": "https://github.com/eventB-Soton/ERTMS-HL3"
    "@6b81638c95ab6cd2397c846ed78f78e6adb5780f developments/HL3_abz2018.zip HL3/",
}

# Attributes holding an Event-B formula, i.e. the P1 denominator.
FORMULA_ATTRS = re.compile(r'org\.eventb\.core\.(?:predicate|assignment|expression)="')


def rows():
    out = []
    for proj in sorted(ORIGINS):
        for p in sorted(glob.glob(f"{ROOT}/corpus/{proj}/*")):
            b = open(p, "rb").read()
            out.append(
                (proj, os.path.basename(p), str(len(b)), hashlib.sha256(b).hexdigest())
            )
    return out


def render(rs):
    lines = [
        "# Corpus pinned by upstream commit. Regenerate: tools/manifest.py",
        "# Never edit by hand; baseline/*.tsv numbers are only valid against these bytes.",
    ]
    lines += [f"# origin\t{k}\t{v}" for k, v in sorted(ORIGINS.items())]
    lines.append("project\tfile\tbytes\tsha256")
    lines += ["\t".join(r) for r in rs]
    return "\n".join(lines) + "\n"


def gates():
    src = sorted(
        glob.glob(f"{ROOT}/corpus/*/*.bum") + glob.glob(f"{ROOT}/corpus/*/*.buc")
    )
    forms, elems = 0, collections.Counter()
    for p in src:
        s = open(p, encoding="utf-8").read()
        forms += len(FORMULA_ATTRS.findall(s))
        elems.update(re.findall(r"<(org\.eventb\.core\.\w+)", s))
    types = pos = 0
    for p in sorted(glob.glob(f"{ROOT}/corpus/*/*.bpo")):
        s = open(p, encoding="utf-8").read()
        types += len(re.findall(r'org\.eventb\.core\.type="', s))
        pos += s.count("<org.eventb.core.poSequent ")
    # Rodin's own discharge record, the P4 bar: psManual="false" is what its provers
    # closed without a human.
    auto = manual = 0
    for p in sorted(glob.glob(f"{ROOT}/corpus/*/*.bps")):
        for a in re.findall(r"<org\.eventb\.core\.psStatus\b([^>]*)>",
                            open(p, encoding="utf-8").read()):
            if 'psManual="true"' in a:
                manual += 1
            else:
                auto += 1
    return src, forms, types, pos, elems, auto, manual


def main():
    check = "--check" in sys.argv
    path = f"{ROOT}/corpus/MANIFEST.tsv"
    text = render(rows())
    if check:
        if not os.path.exists(path) or open(path, encoding="utf-8").read() != text:
            print(
                "corpus drift: MANIFEST.tsv is stale, run tools/manifest.py",
                file=sys.stderr,
            )
            return 1
    else:
        open(path, "w", encoding="utf-8").write(text)

    src, forms, types, pos, elems, auto, manual = gates()
    print(f"P0 source files   {len(src)}")
    print(f"P1 formulas       {forms}")
    print(f"P2 type assertions{types:>6}")
    print(f"P3 PO sequents    {pos}")
    print(f"P4 Rodin baseline {auto} auto, {manual} manual, {auto + manual} discharged")
    print(
        "elements: "
        + "  ".join(f"{k.split('.')[-1]} {v}" for k, v in elems.most_common())
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
