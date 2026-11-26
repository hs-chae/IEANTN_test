#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Deterministic exchange LP scout. All outputs are UNVERIFIED candidates."""
import concurrent.futures, hashlib, importlib.metadata, json, os, resource, sys, time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

OUT=Path(sys.argv[1]);OUT.mkdir(parents=True,exist_ok=False)
CASES=[('36/11',24,10),('36/11',24,20),('36/11',24,40),('36/11',24,60),('4',24,20),('4',24,40)]

def save(p,d):
    tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()

def sample(h,m,G=65536):
    jumps=np.r_[h[:-1]-h[1:],h[-1]]
    modes=np.zeros(2*G)
    modes[1:len(h)+1]=jumps
    y=np.fft.rfft(modes)
    phi=np.empty(G+1);phi[0]=2*np.sum(h)/m
    phi[1:]=np.abs(y[1:].imag)*2*G/(m*np.pi*np.arange(1,G+1))
    return phi

def case(row):
    astr,m,R=row;A=float(Q(astr));n=m*R;d=OUT/f'A{astr.replace("/","_")}-m{m}-R{R}';d.mkdir()
    t0=time.monotonic();u=np.linspace(0,m/2,3601);history=[];res=None
    try:
        for it in range(10):
            # Exact mathematical box transform sampled in floating arithmetic.
            B=(2/m)*np.sinc(u[:,None]/m)*np.cos((2*np.pi/m)*u[:,None]*(np.arange(m,n)+.5))
            base=2*np.sinc(2*u)
            Aub=np.vstack([np.c_[B,-np.ones(len(u))],np.c_[-B,-np.ones(len(u))]])
            bub=np.r_[-base,base];del B
            c=np.r_[np.zeros(n-m),1.]
            res=linprog(c,A_ub=Aub,b_ub=bub,bounds=[(1-A,1)]*(n-m)+[(0,None)],method='highs',options={'time_limit':1200.,'threads':2,'dual_feasibility_tolerance':1e-8,'primal_feasibility_tolerance':1e-8})
            del Aub,bub
            if not res.success:
                history.append({'iteration':it,'points':len(u),'success':False,'status':int(res.status),'message':str(res.message)});break
            h=np.r_[np.ones(m),res.x[:-1]];vals=sample(h,m);idx=np.flatnonzero((vals[1:-1]>=vals[:-2])&(vals[1:-1]>=vals[2:]))+1
            idx=np.r_[0,idx,len(vals)-1];viol=idx[vals[idx]>res.fun+2e-7]
            history.append({'iteration':it,'points':len(u),'lp_M':float(res.fun),'dense_grid_diagnostic_max':float(max(vals)),'dense_violating_extrema':len(viol)})
            # Preserve every solved LP rather than only a favorable selected run.
            save(d/f'iteration-{it}.json',{'status':'UNVERIFIED_FLOATING_SCOUT_NOT_A_BOUND','A':astr,'m':m,'support':R,'history_row':history[-1],'heights':h.tolist()})
            if len(viol)==0:break
            order=viol[np.argsort(vals[viol])[-128:]];u=np.unique(np.r_[u,order*m/(2*65536)])
        witness=None
        if res is not None and res.success:
            # Deterministic coefficient rounding; exact dual constraints enforced.
            wings=[max(Q(1)-Q(astr),min(Q(1),Q(round(float(x)*10**10),10**10)))for x in res.x[:-1]]
            witness={'A':astr,'m':m,'support':R,'search_panels':3600,'wing_heights':[str(x)for x in wings],'sup_upper_bound':'1.21'}
            save(d/'candidate.json',witness)
        result={'status':'COMPLETED_UNVERIFIED_FLOATING_SCOUT'if witness else 'UNSOLVED_SCOUT','parameters':row,'seconds':time.monotonic()-t0,'history':history,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_first_PV':False,'Lean_closed':False}
    except Exception as e:result={'status':'SCOUT_ERROR','parameters':row,'exception':repr(e),'history':history,'seconds':time.monotonic()-t0}
    save(d/'RESULT.json',result);print(json.dumps(result),flush=True);return result

save(OUT/'PLAN.json',{'status':'FROZEN_FLOATING_EXCHANGE_SCOUT_NOT_PROOF','cases':CASES,'iterations':10,'initial_grid_points':3601,'diagnostic_DFT_half_length':65536,'coefficient_denominator':10**10,'seed':'none-deterministic-LP','workers':2,'solver_threads_per_worker':2,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'python':sys.version,'numpy':importlib.metadata.version('numpy'),'scipy':importlib.metadata.version('scipy')})
t=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as ex:results=list(ex.map(case,CASES))
save(OUT/'RESULT.json',{'status':'COMPLETED_FLOATING_SCOUT_NOT_A_CERTIFICATE','results':results,'seconds':time.monotonic()-t,'maximum_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
