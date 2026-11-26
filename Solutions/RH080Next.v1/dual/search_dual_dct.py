#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Dense Chambolle-Pock minimax scout using the orthogonal DCT-IV.
Floating candidate generation only; every proposed cap needs separate verification.
"""
import concurrent.futures,hashlib,importlib.metadata,json,os,resource,sys,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.fft import dct

OUT=Path(sys.argv[1]);OUT.mkdir(parents=True,exist_ok=False)
CASES=[('36/11',24,20),('36/11',24,40),('36/11',24,60),('4',24,20)]
L=16384;ITERATIONS=20000

def save(p,x):
 t=p.with_name('.'+p.name+'.tmp')
 with t.open('x')as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 try:os.link(t,p)
 finally:t.unlink()

def project_l1(v):
 a=np.abs(v)
 if a.sum()<=1:return v
 s=np.sort(a)[::-1];css=np.cumsum(s);idx=np.flatnonzero(s>(css-1)/np.arange(1,len(v)+1));rho=idx[-1];theta=(css[rho]-1)/(rho+1)
 return np.sign(v)*np.maximum(a-theta,0)

def case(row):
 astr,m,R=row;A=float(Q(astr));n=m*R;folder=OUT/f'A{astr.replace("/","_")}-m{m}-R{R}';folder.mkdir();t0=time.monotonic()
 source=Path(__file__).with_name('inputs')/('dual-rh.json'if astr=='36/11'else'dual-grh.json');base=json.load(source.open());initial=np.r_[np.ones(m),[float(Q(v))for v in base['wing_heights']]]
 h=np.zeros(L);h[:len(initial)]=initial;hbar=h.copy();y=np.zeros(L);avg=np.zeros(L);avg_count=0;factor=np.sinc((np.arange(L)+.5)/(2*L));scale=np.sqrt(2*L)/m;step=.95/scale;best=10.;history=[]
 def forward(x):return scale*factor*dct(x,type=4,norm='ortho',workers=1)
 def transpose(v):return scale*dct(factor*v,type=4,norm='ortho',workers=1)
 def inspect(v):
  z=forward(v);origin=abs(2*v[:n].sum()/m);return max(float(np.max(np.abs(z))),origin)
 for i in range(ITERATIONS):
  y=project_l1(y+step*forward(hbar));old=h;h=np.clip(h-step*transpose(y),1-A,1);h[:m]=1;h[n:]=0;hbar=2*h-old
  if i>=1000:avg_count+=1;avg+=(h-avg)/avg_count
  if i%500==0 or i+1==ITERATIONS:
   vals=[(inspect(h),h)]
   if avg_count:vals.append((inspect(avg),avg))
   value,which=min(vals,key=lambda p:p[0]);history.append({'iteration':i+1,'diagnostic_DCT_grid_max':value})
   if value<best:
    best=value;wings=[max(1-Q(astr),min(Q(1),Q(round(float(v)*10**10),10**10)))for v in which[m:n]]
    save(folder/f'candidate-{i+1}.json',{'A':astr,'m':m,'support':R,'search_panels':L,'wing_heights':[str(v)for v in wings],'sup_upper_bound':'1.21'})
    save(folder/f'diagnostic-{i+1}.json',{'status':'UNVERIFIED_FLOATING_CANDIDATE','diagnostic_only_M':value,'iteration':i+1,'seconds':time.monotonic()-t0})
 result={'status':'COMPLETED_FLOATING_DCT_SCOUT_NOT_A_PROOF','parameters':row,'best_sampled_diagnostic_only':best,'iterations':ITERATIONS,'grid_length':L,'seconds':time.monotonic()-t0,'history':history,'source_first_PV':False,'Lean_closed':False};save(folder/'RESULT.json',result);print(json.dumps({k:result[k]for k in ['status','parameters','best_sampled_diagnostic_only','seconds']}),flush=True);return result
save(OUT/'PLAN.json',{'status':'FROZEN_DCT_CP_SCOUT_NOT_PROOF','cases':CASES,'grid_length':L,'iterations':ITERATIONS,'step_ratio':.95,'workers':2,'threads_each':1,'seed':'none-deterministic','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'numpy':importlib.metadata.version('numpy'),'scipy':importlib.metadata.version('scipy'),'orthogonal_operator':'DCT-IV normortho, scale sqrt(2L)/m, sinc((k+.5)/(2L)); unitbox in spectralheights withfirstmfixed1 andaftermRfixed0'})
t=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as ex:results=list(ex.map(case,CASES))
save(OUT/'RESULT.json',{'status':'COMPLETED_FLOATING_SCOUT_NOT_CERTIFIED','seconds':time.monotonic()-t,'maximum_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'results':results})
