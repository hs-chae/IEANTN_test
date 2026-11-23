#!/usr/bin/env python3
"""Exact rational rounded quadrature proposals; all cells rechecked in Lean."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json
from generate_endpoints import grid,build_tree
HERE=Path(__file__).resolve().parent
SCALE=10**12

def ceil(q):return -((-q.numerator)//q.denominator)
def generate():
    up=json.loads((HERE/'ENDPOINT_PROPOSALS.json').read_text())['upper_numerators']
    logs=json.loads((HERE/'LOG_PROPOSALS.json').read_text())['nonnegative_log_upper_numerators']
    z=[];o=[]
    for i in range(7300):
        a=grid(i);b=grid(i+1);d=b-a
        c=Q(40)/a**2 if a>=10 else Q(16,33)
        budget=d/2*Q(up[i]+up[i+1],10**8)+c*d**3/12
        z.append(ceil(budget*SCALE))
        o.append(ceil(budget*Q(logs[i+1],10**8)*SCALE) if i>=100 else 0)
    record=dict(status='EXACT_RATIONAL_PROPOSALS_REQUIRE_KERNEL',rows=7300,scale=SCALE,
                cell0_numerators=z,cell1_numerators=o,total0=sum(z),total1=sum(o),
                upper0=str(Q(sum(z),SCALE)),upper1=str(Q(sum(o),SCALE)),
                all_interval_integrals_proved='Separate endpoint, log, cellwise and whole-consumer proofs required',
                source_first_PV=False)
    text='''import OcticLogEndpointData
namespace RHOcticPush.Moments.Endpoint
set_option maxRecDepth 1000000
set_option Elab.async false

def cap0Numerators : Lean.RArray Nat := '''+build_tree(z)+'''
def cap1Numerators : Lean.RArray Nat := '''+build_tree(o)+'''
def cap0 (i : Nat) : ℚ := (cap0Numerators.get i:ℚ)/1000000000000
def cap1 (i : Nat) : ℚ := (cap1Numerators.get i:ℚ)/1000000000000

def cellRat (i : Nat) : ℚ :=
  let a:=grid i
  let b:=grid (i+1)
  (b-a)/2*(upper i+upper (i+1))+
    (if 10 ≤ a then 40/a^2 else 16/33)*(b-a)^3/12

def arithmeticRow (i : Nat) : Bool :=
  if i < 7300 then decide (cellRat i ≤ cap0 i) &&
    (if 100 ≤ i then decide (cellRat i*logUpper (i+1) ≤ cap1 i) else true)
  else true

def allRow (i : Nat) : Bool := row i &&logRow i &&arithmeticRow i
end RHOcticPush.Moments.Endpoint
'''
    return text,record

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--check',action='store_true');a=p.parse_args();t,r=generate()
    for n,d in [('OcticCellData.lean',t),('CELL_PROPOSALS.json',json.dumps(r,indent=2)+'\n')]:
        f=HERE/n
        if a.check:
            if f.read_text()!=d:raise ValueError('Proposal mismatch:'+n)
        else:f.write_text(d)
    print(json.dumps({k:r[k]for k in ['rows','total0','total1','upper0','upper1']}))
if __name__=='__main__':main()
