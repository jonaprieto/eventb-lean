#!/usr/bin/env python3
"""Resolve complete proof obligations out of Rodin's .bpo files.

A sequent names a hypothesis set, and that set names a parent, and so on up a chain;
the predicates of the whole chain are the hypotheses. The sequent's own poPredicate
elements are the goal. Nothing else in the repo needs this, so it stays a script:
its output is the spike's input, not a build artifact.
"""
import glob
import html
import json
import re
import sys

SET = re.compile(
    r'<org\.eventb\.core\.poPredicateSet name="([^"]+)"([^>]*)>(.*?)</org\.eventb\.core\.poPredicateSet>|'
    r'<org\.eventb\.core\.poPredicateSet name="([^"]+)"([^>]*)/>',
    re.S)
PRED = re.compile(r'<org\.eventb\.core\.poPredicate[^>]*org\.eventb\.core\.predicate="([^"]*)"')
IDENT = re.compile(r'<org\.eventb\.core\.poIdentifier name="([^"]+)" org\.eventb\.core\.type="([^"]*)"')
SEQ = re.compile(
    r'<org\.eventb\.core\.poSequent name="([^"]+)"([^>]*)>(.*?)</org\.eventb\.core\.poSequent>', re.S)
PARENT = re.compile(r'org\.eventb\.core\.parentSet="[^"]*#([^"|]+)"')


def parse_file(path):
    src = open(path, encoding='utf-8').read()
    sets = {}
    for m in SET.finditer(src):
        name = m.group(1) or m.group(4)
        attrs = m.group(2) or m.group(5) or ''
        body = m.group(3) or ''
        parent = PARENT.search(attrs)
        sets[name] = {
            'parent': parent.group(1) if parent else None,
            'preds': [html.unescape(p) for p in PRED.findall(body)],
            'idents': [(n, html.unescape(t)) for n, t in IDENT.findall(body)],
        }
    out = []
    for m in SEQ.finditer(src):
        name, body = m.group(1), m.group(3)
        goals = [html.unescape(p) for p in PRED.findall(body)]
        inner = SET.search(body)
        chain, seen = [], set()
        cur = PARENT.search(inner.group(2) or inner.group(5) or '').group(1) if inner and PARENT.search(
            inner.group(2) or inner.group(5) or '') else None
        while cur and cur in sets and cur not in seen:
            seen.add(cur)
            chain.append(cur)
            cur = sets[cur]['parent']
        hyps, idents = [], []
        for s in reversed(chain):
            hyps += sets[s]['preds']
            idents += sets[s]['idents']
        out.append({'file': path.split('/')[-1][:-4], 'name': name,
                    'kind': name.split('/')[-1], 'idents': idents,
                    'hyps': hyps, 'goal': goals[-1] if goals else None})
    return out


def main():
    pos = []
    for p in sorted(glob.glob('corpus/*/*.bpo')):
        pos += parse_file(p)
    complete = [p for p in pos if p['goal']]
    print(f"sequents {len(pos)}, with a goal {len(complete)}", file=sys.stderr)
    json.dump(complete, open('spike/pos.json', 'w'), ensure_ascii=False, indent=1)


if __name__ == '__main__':
    main()
