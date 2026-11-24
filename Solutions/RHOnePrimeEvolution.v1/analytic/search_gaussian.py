#!/usr/bin/env python3
"""Deterministic finite-grid LP search of CMS Gaussian Fourier witnesses.
Every result remains exploratory until continuum/complex formula bounds are
proved; independent scipy quadrature is a diagnostic, never certification.
"""
from pathlib import Path
import argparse,json,hashlib,time,platform,resource
import numpy as np,scipy
from scipy.special import eval_genlaguerre
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack,eye
from scipy.integrate import quad
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--degrees',default='4,8,12,20,28,40');p.add_argument('--step',type=float,default=.005);p.add_argument('--cutoff',type=float,default=8);p.add_argument('--A',type=float,default=4)
a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output required')
a.out.mkdir(parents=True);start=time.monotonic();rows=[]
x=np.arange(0,a.cutoff+a.step/2,a.step);y=np.arange(1,a.cutoff+a.step/2,a.step)
wx=np.full(len(x),2*a.step);wx[[0,-1]]=a.step
wy=np.full(len(y),2*a.step);wy[[0,-1]]=a.step
for degree in map(int,a.degrees.split(',')):
 tt=time.monotonic();n=degree+1
 B=np.column_stack([eval_genlaguerre(k,-.5,2*np.pi*x*x)*np.exp(-np.pi*x*x) for k in range(n)])
 G=np.column_stack([(-1)**k*eval_genlaguerre(k,-.5,2*np.pi*y*y)*np.exp(-np.pi*y*y) for k in range(n)])
 zero=csr_matrix((len(x),len(y)));zeroy=csr_matrix((len(y),len(x)))
 A=vstack([hstack([csr_matrix(B),-eye(len(x)),zero]),hstack([-csr_matrix(B),-eye(len(x)),zero]),hstack([csr_matrix(G),zeroy,-eye(len(y))]),csr_matrix(np.r_[np.zeros(n),wx,np.zeros(len(y))][None,:])],format='csr')
 rhs=np.r_[np.zeros(2*len(x)+len(y)),1.]
 f0=np.array([eval_genlaguerre(k,-.5,0) for k in range(n)])
 objective=np.r_[-f0,np.zeros(len(x)),a.A*wy]
 bounds=[(None,None)]*n+[(0,None)]*(len(x)+len(y))
 result=linprog(objective,A_ub=A,b_ub=rhs,bounds=bounds,method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
 row={'degree':degree,'status':'LP_FAILED','scipy_status':int(result.status),'message':result.message,'grid_dx':a.step,'grid_cutoff':a.cutoff}
 if result.success:
  coeff=result.x[:n];coeff=coeff/float(f0@coeff)
  # Decimal rounding fixes a reproducible rational candidate source independently
  # of the solver's binary representation. No positivity claim is inferred.
  rational=[format(float(t),'.14g') for t in coeff];coeff=np.array(list(map(float,rational)))
  def F(t):return float(sum(c*eval_genlaguerre(k,-.5,2*np.pi*t*t) for k,c in enumerate(coeff))*np.exp(-np.pi*t*t))
  def Ft(t):return float(sum((-1)**k*c*eval_genlaguerre(k,-.5,2*np.pi*t*t) for k,c in enumerate(coeff))*np.exp(-np.pi*t*t))
  nrm,en=quad(lambda t:2*abs(F(t)),0,12,epsabs=1e-10,epsrel=1e-10,limit=2500)
  leak,el=quad(lambda t:2*max(0,Ft(t)),1,12,epsabs=1e-10,epsrel=1e-10,limit=2500)
  jj=(F(0)-a.A*leak)/nrm
  row.update({'status':'EXPLORATORY_RATIONAL_CANDIDATE_NOT_CERTIFIED','coefficients_decimal_exact_rationals':rational,'basis':'L_n^{-1/2}(2*pi*x^2)*exp(-pi*x^2); FT eigenvalue(-1)^n','F0':F(0),'norm_L1_truncated12':nrm,'positive_FT_leak_truncated12':leak,'quad_reported_error':[en,el],'A':a.A,'J':jj,'inverse_J':1/jj,'LP_grid_objective':-float(result.fun)})
 row['elapsed_seconds']=time.monotonic()-tt;rows.append(row)
 (a.out/f'degree{degree}.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:v for k,v in row.items() if k in ['degree','status','A','J','inverse_J','elapsed_seconds']}),flush=True)
rec={'status':'ORDINARY_EXPLORATION_ONLY_NO_PROOF_OR_PV','python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'A':a.A,'rows':rows,'unresolved':['quadrature rigorous enclosures','sign regions continuum','infinite tails','explicit formula/zero/prime power bounds','explicit onset','kernel Lean numerical attachment']}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n')
