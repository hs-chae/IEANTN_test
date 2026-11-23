#!/usr/bin/env python3
"""Stronger-margin proposal using the identical proved paired GM algorithm.
No point samples are acceptance evidence: this file only proposes rational
whole-real-interval goals, independently checked in Lean kernel mode.
"""
from pathlib import Path
import argparse
import json
from scout607 import cell,Q,K
HERE=Path(__file__).resolve().parent


def run():
    groups=[]
    for name,start,stop,l,u,target in [
        ('Mid',619000000000,620000000000,Q(27803,1024),Q(1779499,65536),Q(1,100)),
        ('High',620000000000,640000000000,Q(889749,32768),Q(1781579,65536),Q(1,80))]:
        todo=[(l,u,0)]
        rows=[]
        while todo:
            a,b,d=todo.pop()
            aa,bb,bd=cell(a,b)
            if bd.l>=target:
                rows.append(dict(l=str(a),u=str(b),a=str(aa),b=str(bb),
                                 interval_lower=str(bd.l),interval_upper=str(bd.u)))
            elif d>=16:
                raise ValueError('No nonempty interval may be skipped')
            else:
                m=(a+b)/2
                todo.extend([(m,b,d+1),(a,m,d+1)])
        rows.sort(key=lambda r:Q(r['l']))
        groups.append(dict(name=name,start=start,stop=stop,target=str(target),
                           lower_log=str(l),upper_log=str(u),rows=rows))
    return dict(status='EXACT_INTERVAL_PROPOSAL_REQUIRES_LEAN',K=str(K),groups=groups,
                analytic_assumptions='Unchanged RH/GM/Buthe nine-input union; same pairBudget',
                exact_exponentials='155term rational Taylor from prior scout; no PV claim')


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a=p.parse_args();result=run();path=HERE/'CORRELATED_STRONG_SCOUT.json'
    if a.check:
        if json.loads(path.read_text())!=result:
            raise ValueError('Proposal mismatch')
    else:path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PROPOSAL_MATCH' if a.check else 'PROPOSAL_GENERATED',
                          groups=[dict(name=g['name'],cells=len(g['rows']))
                                  for g in result['groups']])))
if __name__=='__main__':main()
