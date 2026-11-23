#!/usr/bin/env python3
"""Separate stronger correlated proposal, preserving the completed610 track."""
from pathlib import Path
import argparse
import json
from scout_correlated import I, Q, coef, down, floorq, ceilq, lower_powers, upper_powers

HERE = Path(__file__).resolve().parent
K = Q('2.0796')


def cell(l, u):
    z = I(l,u)
    a = floorq(-Q('.88')+lower_powers(l,u))
    b = ceilq(Q('.68')+upper_powers(l-1))
    root = ((z-1)/2).exp()
    y = (z-1).exp()
    hx = Q('.1386')*(z/2).exp()/(z*(z-5))
    hy = Q('.1386')*root/((z-1)*(z-6))
    g = Q('.0462')*y*root+Q('1.838')*y+Q('1.9851')+Q('.5097')/y
    budget = K*(hx-hy+2*g/(y*(z-1)**2)+Q('1.838')/(z-1)) + \
        (I(1).exp()-K)*(Q('15.51')+hy)
    base = sum([I(coef[j])/z**(j-4) for j in range(4,21)],I(0))-Q(3,8000)
    q = Q('1.95')+Q('3.9')/z+Q('19.5')/z**2
    margin = base+K*z**4*(-z/2).exp()*a-z**5/(z-1)*((1-z)/2).exp()*b - \
        q**2*z**4*(-z).exp()-z**5*(-z).exp()*budget
    return a,b,margin


def run():
    l = Q(1778109,65536)
    u = Q(1778433,65536)
    todo = [(l,u,0)]
    rows = []
    while todo:
        a,b,depth = todo.pop()
        aa,bb,bound = cell(a,b)
        if bound.l >= Q(1,10000):
            rows.append(dict(l=str(a),u=str(b),a=str(aa),b=str(bb),
                             interval_lower=str(bound.l),interval_upper=str(bound.u)))
        elif depth >= 18:
            raise ValueError('Uncertified nonempty interval; no point is skipped')
        else:
            middle=(a+b)/2
            todo.extend([(middle,b,depth+1),(a,middle,depth+1)])
    rows.sort(key=lambda row:Q(row['l']))
    return dict(status='EXACT_RATIONAL_INTERVAL_SCOUT_PENDING_LEAN',start=607000000000,
                stop=610000000000,target='1/10000',K=str(K),lower_log=str(l),upper_log=str(u),
                rows=rows,exponential_bounds='155term exact rational Taylor; independent '
                'whole-real-interval Lean kernel certificates required')


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a=p.parse_args()
    result=run()
    path=HERE/'CORRELATED_607_SCOUT.json'
    if a.check:
        if json.loads(path.read_text())!=result:
            raise ValueError('Scientific proposal differs')
    else:
        path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PROPOSAL_MATCH' if a.check else 'PROPOSAL_GENERATED',
                      'cells':len(result['rows']),
                      'minimum':str(min(Q(row['interval_lower']) for row in result['rows'])),
                      'Lean_acceptance':'Separate'}))


if __name__=='__main__':
    main()
