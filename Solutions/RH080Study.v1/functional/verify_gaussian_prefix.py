#!/usr/bin/env python3
"""Independently replay a frozen Gaussian monomial prefix using the old reference.

Exact basis/input/Fourier association followed by unchanged exact-Sturm/Arb
full-root, full-infinite-integral verification. External verification only.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,hashlib,sys,subprocess,time,resource
sys.path.insert(0,str(Path(__file__).resolve().parent/'primal40'))
from generate_kernel_cells import laguerre_polynomials,source_polynomials

def need(c,msg):
 if not c:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--input',type=Path,required=True);ap.add_argument('--field',choices=['polynomial','P','polynomial_in_y_squared'],required=True);ap.add_argument('--reference',type=Path,required=True);ap.add_argument('--python-flint',type=Path,required=True);ap.add_argument('--target',required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);start=time.monotonic();raw=json.loads(a.input.read_text());p=list(map(Q,raw[a.field]));degree=len(p)-1;basis=laguerre_polynomials(degree);res=p.copy();cs=[Q(0)]*len(p)
 for j in reversed(range(len(p))):
  cs[j]=res[j]/basis[j][j]
  for k in range(j+1):res[k]-=cs[j]*basis[j][k]
 need(not any(res),'Exact basis residual')
 packet={'degree':degree,'coefficients_decimal_exact_rationals':list(map(str,cs)),'original_source_sha256':sha(a.input),'physical_degree':degree*2};derived=a.out/'CANDIDATE.json';derived.write_text(json.dumps(packet,indent=2)+'\n');P,G=source_polynomials(packet);need(P[::2]==p and not any(P[1::2]),'Actual input normalization differs')
 H=[Q(1)];Qout=[Q(0)]*len(P)
 for n in range(len(P)):
  if n%2==0:
   for j,v in enumerate(H):Qout[j]+=(-1)**(n//2)*P[n]*v
  nxt=[Q(0)]*(len(H)+1)
  for j,v in enumerate(H):
   if j:nxt[j-1]+=Q(j,2)*v
   nxt[j+1]-=v
  H=nxt
 need(Qout==G,'Independent monomial/Hermite Fourier association failed')
 frozen=a.out/'reference.py';frozen.write_bytes(a.reference.read_bytes());cmd=['prlimit','--as=68719476736','--','/usr/bin/time','-v','-o',str(a.out/'reference.time'),str(a.python_flint),str(frozen),'--candidate',str(derived),'--out',str(a.out/'reference'),'--prec','256','--root-digits','45','--A','36/11']
 with(a.out/'reference.stdout').open('w')as out,(a.out/'reference.stderr').open('w')as err:r=subprocess.run(cmd,stdout=out,stderr=err,timeout=240)
 need(r.returncode==0,'Reference checker failed; preserve logs')
 # Parse the actual externally certified exact Sturm/Arb result in the same
 # pinned environment; no float comparison is used for acceptance.
 checker='import json,sys;from flint import arb,ctx;ctx.prec=256;d=json.load(open(sys.argv[1]));v=arb(d["enclosures"]["inverse_J"]);target=arb(sys.argv[2]);print(v<target);raise SystemExit(0 if v<target else 1)'
 confirmed=subprocess.run([str(a.python_flint),'-c',checker,str(a.out/'reference/RESULT.json'),a.target],capture_output=True,text=True);need(confirmed.returncode==0,'Independent enclosure does not prove claimed target')
 ref=json.loads((a.out/'reference/RESULT.json').read_text());record={'status':'PASS_INDEPENDENT_EXACT_INPUT_FOURIER_STURM_ARB_FULL_TAIL_TARGET','scope':'External posthoc verification only; no Lean/source-firstPV/retroactiveprimarysuccess or causalclaim','input':str(a.input),'input_sha256':sha(a.input),'input_field':a.field,'Laguerre_degree':degree,'physical_degree':degree*2,'candidate_sha256':sha(derived),'reference_source_sha256':sha(frozen),'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-start,'target':a.target,'enclosures':ref['enclosures'],'reference_receipt_sha256':sha(a.out/'reference/RESULT.json'),'software':ref['software'],'seed':None,'wrapper_sha256':sha(Path(__file__))};tmp=a.out/'RESULT.pending';tmp.write_text(json.dumps(record,indent=2)+'\n');tmp.rename(a.out/'RESULT.json');print(json.dumps({'status':record['status'],'physical_degree':degree*2,'inverse':ref['enclosures']['inverse_J'],'seconds':record['seconds']}))
if __name__=='__main__':main()
