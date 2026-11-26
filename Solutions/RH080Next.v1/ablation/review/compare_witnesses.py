#!/usr/bin/env python3
"""Exact rational comparison of supplied rounded and raw-witness routes."""
import argparse,json,os
from fractions import Fraction as Q
from pathlib import Path
def need(ok,message):
    if not ok:raise ValueError(message)
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    need(not a.output.exists(),'Fresh comparison receipt required')
    q=Q(20582561296,24680948495)
    ns=Q(887721072633027910,10**18);ds=1-4*Q(119725872611533800,8*10**18);ms=Q(546871713113309800,10**18)
    nf=Q(1120475208606944546,10**18);mf=Q(533333333333333333,10**18);df=Q(15,8)*mf
    need(all(v>0 for v in [q,ds,ms,df,mf]),'Positive denominators and maxima required')
    expected={3:Q(193269011844967139,109374342622661960),5:Q(31036198331144443607,8533333333333333328)}
    rows=[]
    for width in [3,5]:
        values={'gaussian_supremum':(Q(width)/q-1)/2,
          'sparse_rounded_attained':(Q(width)-Q(944247,10**6))/Q(1163388,10**6),
          'flat_rounded_attained':(Q(width)-Q(9,8))/Q(16,15),
          'sparse_raw_supremum':(width*ds-ns)/(2*ms),'flat_raw_supremum':(width*df-nf)/(2*mf)}
        route='sparse_raw_supremum' if width==3 else 'flat_raw_supremum';best=values[route]
        need(best==expected[width] and all(best>=v for v in values.values()),'Stronger same-premise route or wrong source constant')
        rounded=max(values['sparse_rounded_attained'],values['flat_rounded_attained']);need(best>rounded,'No strict refinement')
        rows.append(dict(width=width,bounds={k:str(v) for k,v in values.items()},strongest_checked_route=route,raw_minus_rounded=str(best-rounded),raw_minus_rounded_decimal=float(best-rounded),explicit_attained_refinement_midpoint=str((best+rounded)/2),attainment='Every fixed strict deficit below raw supremum is certified; endpoint attainment is not inferred. Rounded affine targets are attained with unspecified positive margins.'))
    result=dict(status='PASS_EXACT_RATIONAL_ROUTE_COMPARISON_NOT_OPTIMALITY',rows=rows,scope='Only the Gaussian inverse, two rounded affine inverse lines, and two supplied certified raw-witness upper-bound routes at widths3and5. No optimality or best-known claim.')
    tmp=a.output.with_name('.'+a.output.name+'.tmp')
    with tmp.open('x') as f:json.dump(result,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,a.output)
    finally:tmp.unlink()
    print('PASS_EXACT_RAW_WITNESS_REFINEMENTS',a.output)
if __name__=='__main__':main()
