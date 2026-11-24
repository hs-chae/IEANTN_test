#!/usr/bin/env python3
"""Untrusted deterministic proposals; every accepted inequality is rechecked in Lean."""
import argparse
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from scout607 import I, Q, coef, floorq, ceilq, lower_powers, upper_powers, K


def profile(t):
    return Q(579, 125) + Q(47, 1000) * (1 + 4 / (t - 8)) * (t / 2).exp() / t**2


def cell(l, u):
    z = I(l, u)
    a = floorq(-Q('.88') + lower_powers(l, u))
    b = ceilq(Q('.68') + upper_powers(l - 1))
    budget = K * profile(z) + I(1).exp() * profile(z - 1)
    base = sum([I(coef[j]) / z**(j - 4) for j in range(4, 21)], I(0)) - Q(3, 8000)
    q = Q('1.95') + Q('3.9') / z + Q('19.5') / z**2
    bound = base + K * z**4 * (-z / 2).exp() * a - \
        z**5 / (z - 1) * ((1 - z) / 2).exp() * b - \
        q**2 * z**4 * (-z).exp() - z**5 * (-z).exp() * budget
    return a, b, bound


def run():
    # Floating logs only propose dyadic endpoints. Lean proves exp(l)<=606b
    # and 610b<=exp(u); these Python logs are never a theorem premise.
    l = Q(math.floor(math.log(606000000000) * 2**20), 2**20)
    u = Q(math.ceil(math.log(610000000000) * 2**20), 2**20)
    todo, rows = [(l, u, 0)], []
    while todo:
        lo, hi, depth = todo.pop()
        a, b, bound = cell(lo, hi)
        if bound.l >= Q(1, 1000):
            rows.append(dict(l=str(lo), u=str(hi), a=str(a), b=str(b),
                             lower=str(bound.l), upper=str(bound.u)))
        elif depth >= 18:
            raise ValueError('A nonempty interval failed; no point may be skipped')
        else:
            middle = (lo + hi) / 2
            todo.extend([(middle, hi, depth + 1), (lo, middle, depth + 1)])
    rows.sort(key=lambda r: Q(r['l']))
    if not rows or Q(rows[0]['l']) != l or Q(rows[-1]['u']) != u:
        raise ValueError('Missing global endpoint')
    if any(a['u'] != b['l'] for a, b in zip(rows, rows[1:])):
        raise ValueError('Gap in proposed interval coverage')
    return dict(status='EXPLORATORY_PROPOSAL_NOT_A_PROOF', start=606000000000,
                stop=610000000000, target='1/1000', K=str(K), lower_log=str(l),
                upper_log=str(u), rows=rows,
                source_change='Adds general Perron and Nicolas to preserved old9 union; '
                              'not a same-premise theorem or published-onset record')


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    result = run()
    output = HERE / 'PROPOSAL.json'
    if a.check:
        if json.loads(output.read_text()) != result:
            raise ValueError('Proposal changed')
    else:
        if output.exists():
            raise ValueError('Preserve previous proposal before replacement')
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status='PROPOSAL_MATCH' if a.check else 'PROPOSAL_GENERATED',
                         cells=len(result['rows']), Lean_acceptance='separate')))


if __name__ == '__main__':
    main()
