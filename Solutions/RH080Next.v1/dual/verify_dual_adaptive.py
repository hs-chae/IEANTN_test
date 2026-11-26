#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Independent complex-Horner/trigonometric replay; no FFT or DFT call.
Arb-assisted supplementary verification, NOT Lean checking or source-first PV.
Every global interval is covered by a directed endpoint/curvature chord bound.
"""
import argparse,gzip,hashlib,json,math,resource,sys,time
from fractions import Fraction as Q
from pathlib import Path
from flint import acb,arb,ctx
from replay_source_dual import ball,need,publish,sha,strict

def main():
 a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--witness',type=Path,required=True);a.add_argument('--run',type=Path,required=True);a.add_argument('--target',required=True);a.add_argument('--bits',type=int,default=160);o=a.parse_args()
 need(not o.run.exists(),'Fresh directory required');need(o.witness.stat().st_size<=2**21,'Oversize witness');d=strict(o.witness.read_bytes())
 need(type(d)is dict and type(d['m'])is int and type(d['support'])is int,'Exact object/integer parameters required');m=d['m'];R=d['support'];need(m>=1 and R>=2,'Positive mesh/support')
 need(type(d['A'])is str and type(d['wing_heights'])is list and all(type(v)is str for v in d['wing_heights']),'Exact rational strings required');A=Q(d['A']);need(A>=1,'Penalty at least1')
 wings=[Q(v)for v in d['wing_heights']];need(len(wings)==m*(R-1),'Wrong number of heights');h=[Q(1)]*m+wings;need(all(1-A<=v<=1 for v in h),'Invalid dual constraint');target=Q(o.target);need(target>0,'Positive bound');need(128<=o.bits<=512,'Unsupported precision')
 o.run.mkdir(parents=True);ctx.prec=o.bits;start=time.monotonic();plan={'status':'FROZEN_INDEPENDENT_ADAPTIVE_HORNER_REPLAY_NOT_PV','source_sha256':sha(Path(__file__)),'common_helper_sha256':sha(Path(__file__).with_name('replay_source_dual.py')),'witness_sha256':sha(o.witness),'A':str(A),'mesh':m,'support':R,'bits':o.bits,'target':str(target),'initial_intervals':32,'maximum_depth':30,'command':[sys.executable,*sys.argv]};publish(o.run/'PLAN.json',plan)
 jumps=[acb(ball(h[j]-(h[j+1]if j+1<len(h)else Q(0))))for j in range(len(h))]
 moment=sum(abs(v)*Q((j+1)**3-j**3,3*m**3)for j,v in enumerate(h));curvature=8*arb.pi()**2*ball(moment);cache={};leaves=[]
 def value(u):
  if u not in cache:
   if u==0:y=abs(ball(2*sum(h)/m)).abs_upper()
   else:
    theta=2*arb.pi()*ball(u)/m;z=acb(0,theta).exp();v=acb(0)
    for jump in reversed(jumps):v=(v+jump)*z
    y=abs(v.imag/(arb.pi()*ball(u))).abs_upper()
   # Integer rational ceiling of an already upward Arb endpoint enclosure.
   cache[u]=(y*2**96).ceil().fmpz().__int__()
  return ball(Q(cache[u],2**96))
 stack=[(Q(j*m,64),Q((j+1)*m,64),0)for j in reversed(range(32))];maxbound=arb(0)
 while stack:
  left,right,depth=stack.pop();v=value(left).max(value(right))+curvature*ball(right-left)**2/8
  if v<ball(target):
   leaves.append([str(left),str(right),cache[left],cache[right]]);maxbound=maxbound.max(v)
  else:
   need(depth<30,'Target not certified at maximum refinement');mid=(left+right)/2;stack.append((mid,right,depth+1));stack.append((left,mid,depth+1))
   need(len(cache)<262144,'More than262144 unique endpoints required; refine strategy before rerun')
 rows=json.dumps({'denominator':2**96,'leaves':leaves},separators=(',',':')).encode();cert=o.run/'adaptive-certificate.json.gz'
 with cert.open('xb')as f:
  with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0)as g:g.write(rows)
 need(sha(o.witness)==plan['witness_sha256']and sha(Path(__file__))==plan['source_sha256'],'Source changed during verification')
 result={'status':'PASS_INDEPENDENT_HORNER_GLOBAL_DUAL_ENCLOSURE_NOT_LEAN_OR_PV','target':str(target),'functional_floor':str(1/target),'leaves':len(leaves),'unique_endpoints':len(cache),'maximum_certified_chord_bound':str(maxbound),'curvature_moment_exact':str(moment),'certificate_sha256':sha(cert),'certificate_bytes':cert.stat().st_size,'seconds':time.monotonic()-start,'maximum_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_first_PV':False,'Lean_numeric_closed':False,'trust':'Native python-flint0.9.0/Arb trigonometric arithmetic and this supplementary verifier; independent of the FFT implementation, not independent of Arb.'};publish(o.run/'RESULT.json',result);print(json.dumps(result))
if __name__=='__main__':main()
