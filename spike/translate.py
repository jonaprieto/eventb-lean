#!/usr/bin/env python3
"""Translate Rodin proof obligations into Lean theorems over Spike.Prelude.

Deliberately a script, not Lean: the spike is a measurement, and a throwaway translator
that is easy to change beats a production one that is not. If the discharge rate is
good, the real version belongs in the POG, emitting terms rather than text.
"""
import json
import re
import sys

# ---- types -------------------------------------------------------------------

def lean_type(t):
    """Rodin type string -> Lean type. Carrier sets become opaque type variables."""
    t = t.strip()
    if t.startswith('ℙ(') and t.endswith(')'):
        return f"Set ({lean_type(t[2:-1])})"
    # Split on top-level × .
    depth, parts, cur = 0, [], ''
    for c in t:
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if c == '×' and depth == 0:
            parts.append(cur); cur = ''
        else:
            cur += c
    parts.append(cur)
    if len(parts) > 1:
        return ' × '.join(lean_type(p) for p in parts)
    if t.startswith('(') and t.endswith(')'):
        return lean_type(t[1:-1])
    if t == 'ℤ':
        return 'Int'
    if t == 'BOOL':
        return 'Bool'
    return t


def carriers(idents):
    """Every capitalised name appearing in a type is a carrier set, i.e. a Lean type."""
    out = []
    for _, t in idents:
        for n in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", t):
            if n not in ('BOOL',) and n not in out:
                out.append(n)
    return out

# ---- expressions -------------------------------------------------------------

BIN = {
    '∧': ' ∧ ', '∨': ' ∨ ', '⇒': ' → ', '⇔': ' ↔ ',
    '=': ' = ', '≠': ' ≠ ', '≤': ' ≤ ', '<': ' < ', '≥': ' ≥ ', '>': ' > ',
    '∈': ' ∈ ', '∉': ' ∉ ', '⊆': ' ⊆ ', '⊂': ' ⊂ ',
    '∪': ' ∪ ', '∩': ' ∩ ', '∖': ' \\ ',
    '+': ' + ', '−': ' - ', '∗': ' * ',
}
FUN2 = {
    '×': 'B.prod', '◁': 'B.domRes', '⩤': 'B.domSub', '▷': 'B.ranRes',
    '⩥': 'B.ranSub', '': 'B.override', '‥': 'B.upto', '∘': 'B.comp',
    '↔': 'B.rel', '⇸': 'B.pfun', '→': 'B.tfun', '⤔': 'B.pinj',
    '↣': 'B.tinj', '⤀': 'B.psurj', '↠': 'B.tsurj', '⤖': 'B.tbij',
}


class Unsupported(Exception):
    pass


# Carrier sets of the obligation being translated. A carrier is a Lean *type*, and its
# use as a value means the whole of that type, so it must not also be bound as a
# variable or the value would shadow the type and coerce everything to a subtype.
CARRIERS = set()


def tr(node):
    k = node[0]
    if k == 'id':
        n = node[1]
        if n in CARRIERS:
            return f'(Set.univ : Set {n})'
        return {'ℤ': '(Set.univ : Set Int)', 'ℕ': 'B.NAT', 'ℕ1': 'B.NAT1',
                'BOOL': '(Set.univ : Set Bool)', 'TRUE': 'true', 'FALSE': 'false',
                '⊤': 'True', '⊥': 'False'}.get(n, n)
    if k == 'num':
        return f'({node[1]} : Int)'
    if k == 'set':
        if not node[1]:
            return '(∅)'
        return '{' + ', '.join(tr(e) for e in node[1]) + '}'
    if k == 'pre':
        op, a = node[1], node[2]
        if op == '¬':
            return f'(¬ {tr(a)})'
        if op == '−':
            return f'(- {tr(a)})'
        if op == 'ℙ':
            return f'(𝒫 {tr(a)})'
        raise Unsupported(op)
    if k == 'post':
        return f'(B.inv {tr(node[2])})'
    if k == 'img':
        return f'(B.image {tr(node[1])} {tr(node[2])})'
    if k == 'app':
        f, a = node[1], node[2]
        if f[0] == 'id' and f[1] == 'dom':
            return f'(B.dom {tr(a)})'
        if f[0] == 'id' and f[1] == 'ran':
            return f'(B.ran {tr(a)})'
        if f[0] == 'id' and f[1] == 'finite':
            return f'(Set.Finite {tr(a)})'
        if f[0] == 'id' and f[1] == 'card':
            return f'((Set.ncard {tr(a)} : Int))'
        if f[0] == 'id' and f[1] in ('min', 'max', 'bool', 'partition', 'union',
                                     'inter', 'id', 'prj1', 'prj2', 'succ', 'pred'):
            raise Unsupported('keyword ' + f[1])
        # Anything else in application position is a user function, and Event-B's `f(x)`
        # is a definite description over a set of pairs.
        return f'(B.app {tr(f)} {tr(a)})'
    if k == 'bin':
        op, a, b = node[1], node[2], node[3]
        if op == '↦':
            return f'({tr(a)}, {tr(b)})'
        if op == '⦂':
            # Ascription on an expression, as in `(∅ ⦂ ℙ(VSS))`. Rodin writes it where
            # the element type cannot be inferred from context, which is exactly where
            # Lean needs it too.
            return f'(({tr(a)}) : {lean_type(render_type(b))})'
        if op == '⊈':
            return f'(¬ ({tr(a)} ⊆ {tr(b)}))'
        if op == '⊄':
            return f'(¬ ({tr(a)} ⊂ {tr(b)}))'
        if op in BIN:
            return f'({tr(a)}{BIN[op]}{tr(b)})'
        if op in FUN2:
            return f'({FUN2[op]} {tr(a)} {tr(b)})'
        raise Unsupported(op)
    if k == 'bind':
        kind, pat, body = node[1], node[2], node[3]
        binders = pattern_binders(pat)
        if kind == '∀':
            return '(∀ ' + ' '.join(binders) + ', ' + tr(body) + ')'
        if kind == '∃':
            return '(∃ ' + ' '.join(binders) + ', ' + tr(body) + ')'
        raise Unsupported('binder ' + kind)
    raise Unsupported(k)


def pattern_binders(pat):
    """`x⦂T, y⦂U` -> ['(x : T)', '(y : U)']."""
    if pat[0] == 'bin' and pat[1] == ',':
        return pattern_binders(pat[2]) + pattern_binders(pat[3])
    if pat[0] == 'bin' and pat[1] == '⦂':
        name, ty = pat[2], pat[3]
        if name[0] != 'id':
            raise Unsupported('ascribed pattern')
        return [f'({name[1]} : {lean_type(render_type(ty))})']
    if pat[0] == 'id':
        return [f'({pat[1]} : _)']
    raise Unsupported('pattern')


def render_type(node):
    """A type appearing inside `⦂` comes back as an expression tree; print it flat."""
    k = node[0]
    if k == 'id':
        return node[1]
    if k == 'pre' and node[1] == 'ℙ':
        return 'ℙ(' + render_type(node[2]) + ')'
    if k == 'bin' and node[1] == '×':
        return render_type(node[2]) + '×' + render_type(node[3])
    raise Unsupported('type expr')
