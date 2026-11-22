#!/usr/bin/env python3
"""Absolute regularized Mellin moments of sinc, with continuous exact bounds."""
from pathlib import Path
import argparse,json,hashlib,time,sys
from rational import F,I,PI,log,trig,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');start=time.monotonic();H=256;h=F(1,500);sh,ch=trig(h);s,c=trig(h/2);neg0=I(0);neg1=I(0);last=-1
def trig_any(q):
 k=0
 while q>F(1,100):q/=2;k+=1
 s,c=trig(q)
 for _ in range(k):s,c=2*s*c,c*c-s*s
 return s,c
for j in range(H*500):
 x=(j+F(1,2))*h
 if j%1000==0:s,c=trig_any(x)
 if x>2:
  neg=max(F(0),-s.l)/x**2;neg0+=neg
  ix=(8*x).__floor__()
  if ix!=last:last=ix;anchor=F(ix,8);la=log(anchor)
  neg1+=neg*(la+(x-anchor)/anchor)
 s,c=s*ch+c*sh,c*ch-s*sh
# The signed sinc Mellin regularized constants are1-gamma and
# ((1-gamma)^2+1-pi^2/12)/2, by Gamma(s)*cos(pi*s/2)/(1-s).
# Euler gamma follows by exact harmonic/log bounds, no float.
N=1024;harm=sum(F(1,k)for k in range(1,N+1));graw=I(harm)-log(N);gamma=I((graw-F(1,2*N)).l,(graw-F(1,2*(N+1))).h)
# Fornegativepart /y, variation<=.75 on[2,infty); withlog<=1.3.
r0=h*neg0+h/2*F('.75')+F(1,H)
r1=h*neg1+h/2*F('1.3')+(log(H)+1)/H
j0=1-gamma+2*r0;j1=((1-gamma)**2+1-PI**2/12)/2+2*r1
need(j0.lt('.701'),'box regularized mass');need(j1.lt('.75'),'box regularized logmoment')
record={'schema':'BOX_REGULARIZED_MOMENTS_V1','status':'PASS','interval_semantics':'Every lower/upper row encloses a rigorous UPPER-BOUND EXPRESSION only; expression.upper bounds the actual integral. row.lower is NOT a lower bound for the actual integral.','phi':'sin(y)/y withphi(0)=1','absolute_regularized_J0':j0.row(),'absolute_regularized_J1':j1.row(),'bounds':{'J0':'.701','J1':'.75'},'parameters':{'cutoff':H,'cells':H*500,'h':'1/500','precision_bits':256},'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'rational_sha256':hashlib.sha256((Path(__file__).parent/'rational.py').read_bytes()).hexdigest(),'python_optimization':sys.flags.optimize,'seconds':time.monotonic()-start,'proof_tier':'directed rational numerical upper expressions + written variation/tail/Mellin proof, not source-firstPV'};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k]for k in ['status','absolute_regularized_J0','absolute_regularized_J1','seconds']},indent=2))
