#!/usr/bin/env python3
"""Deterministic rational interval discovery; separate Lean proofs accept goals.

The interval code here is not trusted or called source-first PV. Its proposed
whole-interval inequalities are independently replayed by LeanCert in kernel mode.
"""
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT/'Solutions/RHLimit.v1/spectral'))
from refined_ram_p8_p1_16 import Q, lo, hi, lower_powers, upper_powers, coef
from ram_cert import down, up
from scout_620_bridge import floorq, ceilq


class I:
    def __init__(self, lower, upper=None):
        self.l = Q(lower)
        self.u = Q(lower if upper is None else upper)

    def __add__(self, other):
        other = interval(other)
        return I(down(self.l+other.l), up(self.u+other.u))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.u, -self.l)

    def __sub__(self, other):
        return self + -interval(other)

    def __rsub__(self, other):
        return interval(other) + -self

    def __mul__(self, other):
        other = interval(other)
        values = [self.l*other.l, self.l*other.u, self.u*other.l, self.u*other.u]
        return I(down(min(values)), up(max(values)))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        if not (other.l > 0 or other.u < 0):
            raise ValueError('Interval divisor contains zero')
        return self*I(down(1/other.u), up(1/other.l))

    def __rtruediv__(self, other):
        return interval(other)/self

    def __pow__(self, n):
        result = I(1)
        for _ in range(n):
            result = result*self
        return result

    def exp(self):
        return I(lo(self.l), hi(self.u))


def interval(value):
    return value if isinstance(value, I) else I(value)


def cell(lower, upper):
    z = I(lower, upper)
    k = Q('2.07978')
    a = floorq(-Q('.88')+lower_powers(lower, upper))
    b = ceilq(Q('.68')+upper_powers(lower-1))
    root = ((z-1)/2).exp()
    y = (z-1).exp()
    hx = Q('.1386')*(z/2).exp()/(z*(z-5))
    hy = Q('.1386')*root/((z-1)*(z-6))
    g = Q('.0462')*y*root+Q('1.838')*y+Q('1.9851')+Q('.5097')/y
    budget = k*(hx-hy+2*g/(y*(z-1)**2)+Q('1.838')/(z-1)) + \
        (I(1).exp()-k)*(Q('15.51')+hy)
    base = sum([I(coef[j])/z**(j-4) for j in range(4,21)], I(0))-Q(3,8000)
    q = Q('1.95')+Q('3.9')/z+Q('19.5')/z**2
    margin = base+k*z**4*(-z/2).exp()*a-z**5/(z-1)*((1-z)/2).exp()*b - \
        q**2*z**4*(-z).exp()-z**5*(-z).exp()*budget
    return a, b, margin


def run():
    lower = Q(6947, 256)
    upper = Q(1779393, 65536)
    todo = [(lower, upper, 0)]
    rows = []
    while todo:
        l, u, depth = todo.pop()
        a, b, bound = cell(l, u)
        if bound.l >= Q(1,1000):
            rows.append(dict(l=str(l), u=str(u), a=str(a), b=str(b),
                             interval_lower=str(bound.l), interval_upper=str(bound.u)))
        elif depth >= 16:
            raise ValueError('No uncertified nonempty interval may be skipped')
        else:
            middle = (l+u)/2
            todo.extend([(middle, u, depth+1), (l, middle, depth+1)])
    rows.sort(key=lambda row: Q(row['l']))
    return dict(status='EXACT_RATIONAL_INTERVAL_SCOUT_PENDING_LEAN', start=610000000000,
                stop=619000000000, target='1/1000', K='103989/50000',
                lower_log=str(lower), upper_log=str(upper), rows=rows,
                exponential_bounds='155term exact rational Taylor frompriorram_cert; '
                'algebraintervalcodeonlyproposesgoals')


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    result = run()
    path = HERE/'CORRELATED_610_SCOUT.json'
    if a.check:
        if json.loads(path.read_text()) != result:
            raise ValueError('Scientific proposal differs')
    else:
        path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'PROPOSAL_MATCH' if a.check else 'PROPOSAL_GENERATED',
                      'cells': len(result['rows']), 'Lean_acceptance': 'Separate'}))


if __name__ == '__main__':
    main()
