#!/usr/bin/env python3
"""Shifted Gaussian packet LP, floating exploration only, no PV/Lean claim."""
import argparse,hashlib,json,math,sys,time,warnings
from decimal import Decimal
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import scipy
from scipy import optimize,sparse,special
A=36/11;SQ=math.sqrt(math.pi)
def need(v,m):
    if not v:raise ValueError(m)
def functions(x,b,s):return np.exp(-math.pi*s*s*(x[:,None]-b[None,:])**2)+np.exp(-math.pi*s*s*(x[:,None]+b[None,:])**2)
def transforms(t,b,s):return 2/s*np.exp(-math.pi*t[:,None]**2/s**2)*np.cos(2*math.pi*t[:,None]*b[None,:])
def Fanti(x,b,s):
    if math.isinf(x):return np.full(len(b),1/s)
    return(special.erf(SQ*s*(x-b))+special.erf(SQ*s*(x+b)))/(2*s)
def Gtail(t,b,s):
    if math.isinf(t):return np.zeros(len(b))
    return np.real(np.exp(-math.pi*t*t/s**2+2j*math.pi*b*t)*special.wofz(SQ*s*b+1j*SQ*t/s))
def integral(c,b,s,wing):
    left=1. if wing else 0.;end=6*s if wing else float(max(b)+6/s);dx=min(.0025,.1/(1+max(b)))if wing else min(.0025,.1/s);x=np.linspace(left,end,math.ceil((end-left)/dx)+1);mat=transforms(x,b,s)if wing else functions(x,b,s);values=mat@c;roots=[]
    def f(t):return float((transforms(np.array([t]),b,s)if wing else functions(np.array([t]),b,s))[0]@c)
    for i in np.flatnonzero(values[:-1]*values[1:]<0):
        if f(x[i])*f(x[i+1])>=0:continue
        r=optimize.brentq(f,x[i],x[i+1],xtol=4e-14,rtol=1e-14)
        if not roots or r-roots[-1]>1e-9:roots.append(r)
    points=[left]+roots+[math.inf];out=0.
    for l,r in zip(points,points[1:]):
        sg=1 if f((l+r)/2 if math.isfinite(r)else max(end,l+1))>=0 else-1
        if wing:
            if sg>0:out+=float((Gtail(l,b,s)-Gtail(r,b,s))@c)
        else:out+=sg*float((Fanti(r,b,s)-Fanti(l,b,s))@c)
    return 2*out,roots
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--sigma',type=float,required=True);ap.add_argument('--max-center',type=float,required=True);ap.add_argument('--spacing',type=float,required=True);ap.add_argument('--dx',type=float,default=.004);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--threads',type=int,default=2);a=ap.parse_args();need(not a.out.exists(),'Freshoutput');a.out.mkdir(parents=True);started=time.monotonic();s=a.sigma;b=np.linspace(0,a.max_center,round(a.max_center/a.spacing)+1);n=len(b)
    x=np.arange(a.dx/2,max(b)+6/s,a.dx);t=np.arange(1+a.dx/2,6*s,a.dx);B=functions(x,b,s);G=transforms(t,b,s);N,M=len(x),len(t);need(M>0,'winggrid')
    bc=sparse.csr_matrix(B);gc=sparse.csr_matrix(G);Aub=sparse.vstack([sparse.hstack([bc,-sparse.eye(N),sparse.csr_matrix((N,M))]),sparse.hstack([-bc,-sparse.eye(N),sparse.csr_matrix((N,M))]),sparse.hstack([gc,sparse.csr_matrix((M,N)),-sparse.eye(M)])],format='csr');f0=2*np.exp(-math.pi*s*s*b*b);eq=sparse.csr_matrix(np.r_[f0,np.zeros(N+M)][None,:]);r=.83394544;hist=[]
    for k in range(3):
        cost=np.r_[np.zeros(n),np.full(N,2*a.dx),np.full(M,2*a.dx*r*A)]
        with warnings.catch_warnings(record=True)as ww:
            p=optimize.linprog(cost,A_ub=Aub,b_ub=np.zeros(2*N+M),A_eq=eq,b_eq=[1.],bounds=[(None,None)]*n+[(0,None)]*(N+M),method='highs-ipm',options={'threads':a.threads,'random_seed':0,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-11})
        need(p.success,p.message);c=p.x[:n];c/=f0@c;Ntrue,nr=integral(c,b,s,False);J,jr=integral(c,b,s,True);q=Ntrue/(1-A*J);hist.append(dict(iteration=k,LPobjective=float(p.fun),q=q,norm=Ntrue,J=J,normroots=len(nr),wingroots=len(jr),solver=p.message,warnings=[str(z.message)for z in ww]));print(json.dumps(dict(sigma=s,B=max(b),spacing=a.spacing,**hist[-1])),flush=True);r=q
    packet={'family':'even_translated_gaussian_packets','sigma':str(a.sigma),'centers':list(map(str,b)),'coefficients':[str(Q(Decimal(str(z)).quantize(Decimal('1e-22'))))for z in c],'searched_ratio':q,'status':'FLOATING_UNCERTIFIED'};(a.out/'CANDIDATE.json').write_text(json.dumps(packet,indent=2)+'\n');res={'status':'FLOATING_TRANSLATED_GAUSSIAN_SEARCH_NOT_A_CERTIFICATE_OR_PV','sigma':s,'max_center':float(max(b)),'spacing':a.spacing,'basis_dimension':n,'ratio':q,'norm':Ntrue,'J':J,'history':hist,'normroots':nr,'wingroots':jr,'seconds':time.monotonic()-started,'seed':0,'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(a.out/'RESULT.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:res[k]for k in ['status','sigma','max_center','spacing','ratio','seconds']}),flush=True)
if __name__=='__main__':main()
