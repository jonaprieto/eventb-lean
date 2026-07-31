#!/usr/bin/env python3
"""Emit a Lean file of proof obligations, one theorem each, and report coverage."""
import json
import subprocess
import sys
sys.path.insert(0, 'spike')
import translate
from translate import tr, lean_type, carriers, Unsupported

pos = json.load(open('spike/pos.json'))

# One astdump call for every formula, keyed by position.
flat, index = [], []
for i, p in enumerate(pos):
    for h in p['hyps']:
        index.append((i, 'h')); flat.append(h.replace('\n', ' '))
    index.append((i, 'g')); flat.append(p['goal'].replace('\n', ' '))
open('/tmp/spike-in.txt', 'w').write('\n'.join(flat))
out = subprocess.run(['./.lake/build/bin/astdump', '/tmp/spike-in.txt'],
                     capture_output=True, text=True).stdout.strip().split('\n')
assert len(out) == len(flat), f"{len(out)} != {len(flat)}"
asts = [json.loads(o) for o in out]
for (i, role), a in zip(index, asts):
    pos[i].setdefault('hyp_ast', [])
    if role == 'h':
        pos[i]['hyp_ast'].append(a)
    else:
        pos[i]['goal_ast'] = a

ok, bad, examples = [], {}, {}
for p in pos:
    try:
        cs = carriers(p['idents'])
        translate.CARRIERS = set(cs)
        binders = [f"({c} : Type)" for c in cs]
        binders += [f"[Nonempty {c}]" for c in cs]
        # A carrier used as a value is `Set.univ`, so it gets no variable of its own.
        binders += [f"({n} : {lean_type(t)})" for n, t in p['idents'] if n not in cs]
        hyps = [f"(h{j} : {tr(a)})" for j, a in enumerate(p.get('hyp_ast', []))]
        goal = tr(p['goal_ast'])
        ok.append((p, binders + hyps, goal))
    except Unsupported as e:
        bad[str(e)] = bad.get(str(e), 0) + 1
        examples.setdefault(str(e), p['goal'][:95])
    except Exception as e:
        bad[type(e).__name__ + ': ' + str(e)[:40]] = bad.get(type(e).__name__ + ': ' + str(e)[:40], 0) + 1

print(f"translated {len(ok)}/{len(pos)}", file=sys.stderr)
for k, v in sorted(bad.items(), key=lambda x: -x[1])[:10]:
    print(f"  {v:5d}  {k:22s} e.g. {examples.get(k,'')}", file=sys.stderr)

TACTICS = sys.argv[1] if len(sys.argv) > 1 else 'try grind'
sample = ok
if len(sys.argv) > 2:
    sample = ok[:int(sys.argv[2])]
lines = ['import Spike.Prelude', 'import Mathlib.Tactic', '',
         'set_option maxHeartbeats 400000', 'set_option maxErrors 10000',
         'set_option autoImplicit false', 'open B', '']
for k, (p, binders, goal) in enumerate(sample):
    name = 'po' + str(k)
    lines.append(f'-- {p["file"]} {p["name"]}')
    lines.append(f'theorem {name} ' + ' '.join(binders) + f' :\n    {goal} := by')
    lines.append(f'  {TACTICS}')
    lines.append('')
open('spike/Spike/Obligations.lean', 'w').write('\n'.join(lines))
print(f"wrote {len(sample)} theorems", file=sys.stderr)
