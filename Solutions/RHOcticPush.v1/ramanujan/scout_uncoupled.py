#!/usr/bin/env python3
"""Regenerate the first, independently preserved b5/unpaired exact proposals."""
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT/'Solutions/RHLimit.v1/spectral'))
from refined_ram_p8_p1_16 import Q, p, lo, hi, lower_powers, upper_powers, coef, down
from scout_620_bridge import floorq, ceilq


def shift(l, u):
    return Q('0.1386')/(l-5)+Q('15.51')*u*hi(-l/2)


def cell(l, u):
    c = floorq(-Q('.88')-shift(l,u)+lower_powers(l,u))
    d = ceilq(Q('.68')+shift(l-1,u-1)+upper_powers(l-1))
    base = sum(coef[j]/u**(j-4) for j in range(4,21))-Q(3,8000)
    margin = down(base-d*l**5/(l-1)*hi((1-l)/2) +
                  2*p(20,u)*c*u**4*lo(-u/2)-c*c*l**4*hi(-l))
    return c, d, margin


def run():
    rows = []
    summary = []
    # Proposed lower log endpoints are independently proved by Lean exp checks.
    bands = [('low',617500000000,619000000000,Q(1,5000),Q(7116933,262144)),
             ('mid',619000000000,620000000000,Q(3,2000),Q(7117569,262144)),
             ('high',620000000000,640000000000,Q(1,400),Q(889749,32768))]
    outputs = {r['n']:r['output'] for r in json.loads((HERE/'C_LOG_EXECUTION.json').read_text())['rows']}
    for name, start, stop, target, lower in bands:
        upper = Q(outputs[stop],2**40)
        todo = [(lower,upper,0)]
        accepted = []
        while todo:
            l, u, depth = todo.pop()
            c, d, margin = cell(l,u)
            if margin >= target:
                accepted.append((l,u,c,d,margin))
            elif depth >= 22:
                raise ValueError('Uncertified nonempty cell')
            else:
                middle = (l+u)/2
                todo.extend([(middle,u,depth+1),(l,middle,depth+1)])
        accepted.sort()
        summary.append(dict(band=name,start=start,stop=stop,target=str(target),
                            lower_log_endpoint=str(lower),upper_log_endpoint=str(upper),
                            cells=len(accepted),
                            minimum_exact_lower_enclosure=str(min(t[4] for t in accepted))))
        for l,u,c,d,margin in accepted:
            rows.append(dict(band=name,start=start,stop=stop,target=str(target),
                             l=str(l),u=str(u),c=str(c),d=str(d),margin_exact_lower=str(margin)))
    return dict(schema='RAM_OCTIC_PUSH_EXACT_RATIONAL_SCOUT_V1',
                status='DISCOVERY_ONLY_PENDING_LEAN_KERNEL_CERTIFICATION',source_first_PV=False,
                method='Adaptive complete closed logarithmic intervals, exact rational expTaylor bounds; '
                'proposed lower log endpoints frombinary64 are separately checked by Lean. '
                'Upper endpoints areactual C-source outputs and proved viaHighLogInputs.',
                GM_profile='15.51+.1386sqrtx/[logx(logx−5)]',
                square_remainder='3/8000, provedunconditionallyL≥27', bands=summary, rows=rows,seeds=None)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a = p.parse_args()
    result = run()
    path = HERE/'SCOUT_FRONTIER.json'
    if a.check:
        if json.loads(path.read_text()) != result:
            raise ValueError('Exact scientific goals differ')
    else:
        path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PROPOSAL_MATCH' if a.check else 'PROPOSAL_GENERATED',
                      'cells':len(result['rows']),'Lean_acceptance':'Separate'}))


if __name__ == '__main__':
    main()
