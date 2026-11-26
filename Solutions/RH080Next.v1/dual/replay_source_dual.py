#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Guarded external-Arb replay of the primary rational-step dual, never PV."""
import argparse,hashlib,importlib.metadata,json,math,os,resource,sys,time
from fractions import Fraction as Q
from pathlib import Path
from flint import acb,arb,ctx,fmpq

def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict(raw):
    def pairs(rows):
        d={}
        for k,v in rows:need(k not in d,'Duplicate JSON key');d[k]=v
        return d
    return json.loads(raw,object_pairs_hook=pairs,parse_float=lambda s:(_ for _ in()).throw(ValueError('Floating JSON is unsupported')),parse_constant=lambda s:(_ for _ in()).throw(ValueError(s)))
def publish(p,x):
    need(not p.exists(),'Fresh receipt required');t=p.with_name('.'+p.name+'.tmp')
    with t.open('x')as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def ball(q):return arb(fmpq(q.numerator,q.denominator))
def main():
    a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--witness',type=Path,required=True);a.add_argument('--run',type=Path,required=True);a.add_argument('--panels',type=int,default=262144);a.add_argument('--bits',type=int,default=128);a.add_argument('--target');o=a.parse_args()
    need(not os.path.lexists(o.run),'Fresh run directory required');need(o.witness.stat().st_size<=2*1024**2,'Witness exceeds supported size');d=strict(o.witness.read_bytes());need(type(d)is dict,'Object witness required')
    need(type(d['m'])is int and type(d['support'])is int and d['m']>=1 and d['support']>=2,'Exact positive integer mesh/support required')
    m=d['m'];R=d['support'];need(type(d['A'])is str,'Exact rational penalty string required');A=Q(d['A']);need(A>=1,'Penalty must be at least1')
    need(type(d['wing_heights'])is list and all(type(v)is str for v in d['wing_heights']),'Rational string wing list required');wings=[Q(v)for v in d['wing_heights']];need(len(wings)==m*(R-1),'Exact wing population required');h=[Q(1)]*m+wings
    need(all(1-A<=v<=1 for v in h),'Dual pointwise constraint violated')
    G=o.panels;need(type(G)is int and 1<=G<=2**24 and G&(G-1)==0 and 2*G>len(h),'DFT length/power/population invalid');need(96<=o.bits<=512,'Precision out of supported replay range')
    need(o.target is not None or type(d['sup_upper_bound'])is str,'Exact rational target string required');target=Q(o.target or d['sup_upper_bound']);need(target>0,'Positive exact target required')
    need(importlib.metadata.version('python-flint')=='0.9.0','Pinned python-flint0.9.0 required')
    o.run.mkdir(parents=True);start=time.monotonic();ctx.prec=o.bits
    plan={'status':'FROZEN_EXTERNAL_INTERVAL_REPLAY_PLAN_NOT_LEAN_OR_PV','controller_sha256':sha(Path(__file__)),'witness_sha256':sha(o.witness),'A':str(A),'mesh':m,'support':R,'panels':G,'bits':o.bits,'target':str(target),'python':sys.version,'python_flint':'0.9.0','optimization':sys.flags.optimize,'command':[sys.executable,*sys.argv]};publish(o.run/'PLAN.json',plan)
    jumps=[h[j]-(h[j+1]if j+1<len(h)else Q(0))for j in range(len(h))]
    modes=[acb(0)]*(2*G)
    for j,v in enumerate(jumps,1):modes[j]=acb(ball(v))
    values=acb.dft(modes);peak=abs(ball(2*sum(h)/m)).abs_upper();scale=2*G/(m*arb.pi());peak_index=0
    for k in range(1,G+1):
        v=(abs(values[k].imag)*scale/k).abs_upper()
        if v>peak:peak_index=k
        peak=peak.max(v)
    moment=sum(abs(v)*Q((j+1)**3-j**3,3*m**3)for j,v in enumerate(h))
    curvature=8*arb.pi()**2*ball(moment);allowance=curvature*ball(Q(m,2*G))**2/8;upper=peak+allowance
    need(upper<ball(target),'Actual directed-Arb global upper bound does not meet target')
    need(sha(o.witness)==plan['witness_sha256']and sha(Path(__file__))==plan['controller_sha256'],'Source changed during replay')
    result={'status':'PASS_RATIONAL_STEP_DUAL_GLOBAL_ENCLOSURE_EXTERNAL_ARBITRARY_PRECISION_NOT_LEAN_OR_PV','A':str(A),'mesh':m,'support':R,'panels':G,'bits':o.bits,'verified_strict_upper_target':str(target),'reciprocal_functional_floor':str(1/target),'sampled_maximum_Arb_enclosure':str(peak),'peak_index_diagnostic_only':peak_index,'second_derivative_moment_exact':str(moment),'interpolation_allowance_Arb_enclosure':str(allowance),'global_supremum_Arb_enclosure':str(upper),'seconds':time.monotonic()-start,'maximum_process_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'plan_sha256':sha(o.run/'PLAN.json'),'written_continuum_argument':'Even step box transform; sine numerator odd and mesh-periodic; fold to[0,m/2]; derivative curvature chord error; no finite sampling claim without interpolation allowance.','class_boundary':'Full CMS real-even class is now covered by CMSWeakDuality.weak_duality_even_cms via kernel-proved Abel inversion. This native-Arb supremum certificate remains outside Lean and is not PV.','source_first_PV':False,'Lean_closed':False};publish(o.run/'RESULT.json',result)
    print(json.dumps({k:result[k]for k in ['status','verified_strict_upper_target','reciprocal_functional_floor','seconds','maximum_process_RSS_KiB']}))
if __name__=='__main__':main()
