#!/usr/bin/env python3
"""Attribute Lean errors to the theorem that contains them.

Errors are reported at the failing tactic's line, not at the `theorem` line, so
comparing error lines against declaration lines counts every theorem as passing. Map
each error line to the nearest preceding declaration instead.
"""
import re
import sys

src = open('spike/Spike/Obligations.lean', encoding='utf-8').read().split('\n')
starts = [(i + 1, l.split()[1]) for i, l in enumerate(src) if l.startswith('theorem')]
log = open(sys.argv[1], encoding='utf-8').read()

bad = set()
for m in re.finditer(r'Obligations\.lean:(\d+):\d+: error', log):
    line = int(m.group(1))
    owner = None
    for ln, name in starts:
        if ln <= line:
            owner = name
        else:
            break
    if owner:
        bad.add(owner)

total = len(starts)
print(f"attempted {total}   failed {len(bad)}   closed {total - len(bad)}")
if len(sys.argv) > 2:
    open(sys.argv[2], 'w').write('\n'.join(sorted(bad)))
