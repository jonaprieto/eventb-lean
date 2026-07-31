#!/usr/bin/env python3
"""Resolve complete proof obligations out of Rodin's .bpo files.

Uses a real XML parse: predicate sets nest, and a regex pairs the wrong open and close
tags, which silently produced sequents with no hypotheses at all.

A sequent names a hypothesis set; that set names a parent, and so on up a chain. The
predicates and identifiers of the whole chain are the context. The sequent's own
poPredicate children are the goal.
"""
import glob
import json
import sys
import xml.etree.ElementTree as ET

CORE = 'org.eventb.core.'


def attr(e, name):
    return e.get(CORE + name)


def last_segment(ref):
    return ref.split('#')[-1] if ref else None


def parse_file(path):
    root = ET.parse(path).getroot()
    sets = {}
    for e in root.iter(CORE + 'poPredicateSet'):
        sets[e.get('name')] = {
            'parent': last_segment(attr(e, 'parentSet')),
            'preds': [attr(p, 'predicate') for p in e.findall(CORE + 'poPredicate')],
            'idents': [(i.get('name'), attr(i, 'type'))
                       for i in e.findall(CORE + 'poIdentifier')],
        }
    out = []
    for seq in root.findall(CORE + 'poSequent'):
        goals = [attr(p, 'predicate') for p in seq.findall(CORE + 'poPredicate')]
        inner = seq.find(CORE + 'poPredicateSet')
        cur = last_segment(attr(inner, 'parentSet')) if inner is not None else None
        chain, seen = [], set()
        while cur and cur in sets and cur not in seen:
            seen.add(cur)
            chain.append(cur)
            cur = sets[cur]['parent']
        hyps, idents = [], []
        for s in reversed(chain):
            hyps += [p for p in sets[s]['preds'] if p]
            idents += sets[s]['idents']
        # The set attached to the sequent may itself carry predicates and identifiers.
        if inner is not None:
            hyps += [attr(p, 'predicate') for p in inner.findall(CORE + 'poPredicate')]
            idents += [(i.get('name'), attr(i, 'type'))
                       for i in inner.findall(CORE + 'poIdentifier')]
        seen_names = set()
        uniq = []
        for n, t in idents:
            if n not in seen_names:
                seen_names.add(n)
                uniq.append((n, t))
        out.append({'file': path.split('/')[-1][:-4], 'name': seq.get('name'),
                    'kind': seq.get('name').split('/')[-1], 'idents': uniq,
                    'hyps': hyps, 'goal': goals[-1] if goals else None})
    return out


def main():
    pos = []
    for p in sorted(glob.glob('corpus/*/*.bpo')):
        pos += parse_file(p)
    complete = [p for p in pos if p['goal']]
    n_id = sum(1 for p in complete if p['idents'])
    n_hy = sum(1 for p in complete if p['hyps'])
    print(f"sequents {len(pos)}, with a goal {len(complete)}, "
          f"with identifiers {n_id}, with hypotheses {n_hy}", file=sys.stderr)
    json.dump(complete, open('spike/pos.json', 'w'), ensure_ascii=False, indent=1)


if __name__ == '__main__':
    main()
