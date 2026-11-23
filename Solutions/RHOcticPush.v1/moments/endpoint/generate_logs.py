#!/usr/bin/env python3
"""Rational log endpoint proposals, independently checked by the Lean kernel."""
from pathlib import Path
import argparse,json,mpmath as mp
from generate_endpoints import grid,build_tree
HERE=Path(__file__).resolve().parent

def generate():
    mp.mp.dps=100
    data=[]
    for i in range(7301):
        q=grid(i)
        value=0 if q<=1 else int(mp.ceil(mp.log(mp.mpf(q.numerator)/q.denominator)*100000000))+1
        data.append(value)
    text='''import OcticEndpointData
namespace RHOcticPush.Moments.Endpoint
open LeanCert.Core LeanCert.Engine LeanCert.Validity
set_option maxRecDepth 1000000
set_option Elab.async false

def logNumerators : Lean.RArray Nat := '''+build_tree(data)+'''
def logUpper (i : Nat) : ℚ := (logNumerators.get i:ℚ)/100000000

def logRow (i : Nat) : Bool :=
  if i=0 then decide ((0:ℚ) ≤ logUpper i)
  else checkUpperBound (.log (.var 0)) (point (grid i)) (logUpper i) cfg
end RHOcticPush.Moments.Endpoint
'''
    record=dict(status='PROPOSALS_REQUIRE_KERNEL_CHECKS',rows=7301,scale=100000000,
                nonnegative_log_upper_numerators=data,rounding='0 forq≤1;ceil(logq*1e8)+1 otherwise',
                proposer='mpmath',version=mp.__version__,decimal_precision=100,source_first_PV=False)
    return text,record

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--check',action='store_true');a=p.parse_args();t,r=generate()
    for name,data in [('OcticLogEndpointData.lean',t),('LOG_PROPOSALS.json',json.dumps(r,indent=2)+'\n')]:
        f=HERE/name
        if a.check:
            if f.read_text()!=data:raise ValueError('Proposal mismatch:'+name)
        else:f.write_text(data)
    print(json.dumps(dict(status='PROPOSALS_MATCH' if a.check else 'PROPOSALS_GENERATED',rows=7301)))
if __name__=='__main__':main()
