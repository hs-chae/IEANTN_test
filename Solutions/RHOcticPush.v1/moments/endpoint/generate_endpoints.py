#!/usr/bin/env python3
"""Propose rational endpoint bounds; only Lean kernel checks grant acceptance."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,hashlib,json,mpmath as mp
HERE=Path(__file__).resolve().parent
SCALE=100000000

def grid(i):
    return Q(i,100) if i<=1000 else Q(10)+Q(i-1000,20) if i<=2800 else Q(100)+Q(i-2800,5)

def build_tree(values,start=0):
    if len(values)==1:return f'(.leaf {values[0]})'
    n=len(values)//2
    return f'(.branch {start+n} '+build_tree(values[:n],start)+' '+build_tree(values[n:],start+n)+')'

def generate():
    mp.mp.dps=100
    ups=[]
    for i in range(7301):
        if i==0:v=mp.mpf(16)/9
        else:
            q=grid(i);x=mp.mpf(q.numerator)/q.denominator
            a=-16/x**2+672/x**4-13440/x**6+80640/x**8
            b=112/x**3-3360/x**5+40320/x**7-80640/x**9
            v=abs(a*mp.cos(x)+b*mp.sin(x))
        radius=mp.mpf('0.0001')/(1+(mp.mpf(grid(i).numerator)/grid(i).denominator))
        ups.append(int(mp.ceil((v+radius)*SCALE))+1)
    data='''import OcticEndpointChecker
import Lean.Data.RArray
namespace RHOcticPush.Moments.Endpoint
set_option maxRecDepth 1000000
set_option Elab.async false

def grid (i : Nat) : ℚ :=
  if i ≤ 1000 then (i:ℚ)/100
  else if i ≤ 2800 then 10+((i-1000:Nat):ℚ)/20
  else 100+((i-2800:Nat):ℚ)/5

def upperNumerators : Lean.RArray Nat := '''+build_tree(ups)+'''
def upper (i : Nat) : ℚ := (upperNumerators.get i:ℚ)/100000000

def row (i : Nat) : Bool :=
  if i=0 then decide ((16/9:ℚ) ≤ upper i) else check (grid i) (upper i)
end RHOcticPush.Moments.Endpoint
'''
    return data,dict(status='UNTRUSTED_PROPOSAL_ALL_ROWS_REQUIRE_KERNEL_CHECKS',scale=SCALE,rows=len(ups),upper_numerators=ups,
                     grid='i/100(i≤1000);10+(i−1000)/20(i≤2800);100+(i−2800)/5 otherwise',
                     proposer='mpmath',version=mp.__version__,decimal_precision=mp.mp.dps,rounding='ceil((abs(F(q))+1e-4/(1+q))*1e8)+1',enclosure_radius='1e-4/(1+q) compensates verified pi range-reduction width; all rows must independently pass kernel checks',
                     random_seed=None,source_first_PV=False)

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--check',action='store_true');a=p.parse_args()
    text,record=generate()
    for name,content in [('OcticEndpointData.lean',text),('ENDPOINT_PROPOSALS.json',json.dumps(record,indent=2)+'\n')]:
        path=HERE/name
        if a.check:
            if path.read_text()!=content:raise ValueError('Deterministic proposal mismatch:'+name)
        else:path.write_text(content)
    print(json.dumps(dict(status='PROPOSALS_MATCH' if a.check else 'PROPOSALS_GENERATED',rows=record['rows'],Lean_acceptance='Separate')))
if __name__=='__main__':main()
