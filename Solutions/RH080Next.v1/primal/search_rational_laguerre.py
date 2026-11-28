#!/usr/bin/env python3
"""Exponential spectral Laguerre / rational physical family, exploratory only.

G(t)=exp(-a|t|) sum c_j L_j(2a|t|).
F(x)=(2/a) cos(theta)^2 P(2theta), theta=atan(2pi*x/a),
P(phi)=sum_j c_j[1+2sum_{k=1}^j(-1)^k cos(kphi)].
Thus ||F||1=(1/pi)int_0^pi|P(phi)|dphi. F(0)=2/a sum(-1)^j c_j.
These identities require a formal Fourier/Laplace proof before any accepted use.
"""
import argparse,hashlib,json,math,sys,time,warnings
from decimal import Decimal
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import scipy
from scipy import optimize,sparse
from search_affine_lp import evaluator,norm_roots,need
A=36/11
def lag(x,n):
    x=np.atleast_1d(x).astype(np.longdouble);p=np.exp(-x);out=[np.array(p,dtype=float)]
    if n:
        q=(1-2*x)*p;out.append(np.array(q,dtype=float))
        for j in range(1,n):p,q=q,((2*j+1-2*x)*q-j*p)/(j+1);out.append(np.array(q,dtype=float))
    return np.array(out).T
def tail(x,n):
    if math.isinf(x):return np.zeros(n+1)
    g=lag([x],n)[0];out=[];acc=0.
    for j in range(n+1):out.append(g[j]+2*((-1)**j)*acc);acc+=((-1)**j)*g[j]
    return np.array(out)
def positive_integral(c,a,step=.005):
    n=len(c)-1;end=max(a+30.,4*n+50.);x=np.linspace(a,end,math.ceil((end-a)/step)+1);b=lag(x,n);v=b@c;roots=[]
    def f(z):return float(lag([z],n)[0]@c)
    for i in np.flatnonzero(v[:-1]*v[1:]<0):
        if f(x[i])*f(x[i+1])>=0:continue
        r=optimize.brentq(f,x[i],x[i+1],xtol=3e-14,rtol=1e-14)
        if not roots or r-roots[-1]>1e-9:roots.append(r)
    points=[a]+roots+[math.inf];total=0.
    for l,r in zip(points,points[1:]):
        mid=(l+r)/2 if math.isfinite(r)else max(end,l+10.)
        if f(mid)>0:total+=float((tail(l,n)-tail(r,n))@c)
    return total*2/a,roots
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--degree',type=int,required=True);ap.add_argument('--a',type=float,required=True);ap.add_argument('--wing-step',type=float,default=.02);ap.add_argument('--norm-grid',type=int,default=8192);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--threads',type=int,default=2);a=ap.parse_args();need(not a.out.exists(),'Freshoutput');a.out.mkdir(parents=True);began=time.monotonic();n=a.degree;alpha=a.a;N=a.norm_grid
    lib,cmd=evaluator(Path(__file__).with_name('floating_trig.c'),a.out)
    phi=math.pi*(np.arange(N)+.5)/N;coses=2*np.cos(phi[:,None]*np.arange(1,n+1)[None,:])*((-1.)**np.arange(1,n+1))[None,:];B=np.c_[np.ones(N),1+np.cumsum(coses,axis=1)]
    end=max(alpha+30.,4*n+50.);M=math.ceil((end-alpha)/a.wing_step);dv=(end-alpha)/M;ys=alpha+dv*(np.arange(M)+.5);G=lag(ys,n)
    keep=np.max(abs(G),axis=1)>1e-16;G=G[keep];M=len(G)
    bc=sparse.csr_matrix(B);gc=sparse.csr_matrix(G);zNM=sparse.csr_matrix((N,M));zMN=sparse.csr_matrix((M,N));Aub=sparse.vstack([sparse.hstack([bc,-sparse.eye(N),zNM]),sparse.hstack([-bc,-sparse.eye(N),zNM]),sparse.hstack([gc,zMN,-sparse.eye(M)])],format='csr');eq=sparse.csr_matrix(np.r_[2/alpha*((-1.)**np.arange(n+1)),np.zeros(N+M)][None,:]);r=.83394544;history=[]
    for it in range(3):
        cost=np.r_[np.zeros(n+1),np.full(N,1/N),np.full(M,r*A*2/alpha*dv)]
        with warnings.catch_warnings(record=True)as ww:
            p=optimize.linprog(cost,A_ub=Aub,b_ub=np.zeros(2*N+M),A_eq=eq,b_eq=[1.],bounds=[(None,None)]*(n+1)+[(0,None)]*(N+M),method='highs-ipm',options={'threads':a.threads,'random_seed':0,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-11})
        need(p.success,p.message);c=p.x[:n+1];c/=float(2/alpha*((-1.)**np.arange(n+1))@c)
        w=np.ascontiguousarray(np.r_[sum(c),((-1.)**np.arange(1,n+1))*np.cumsum(c[::-1])[::-1][1:]])
        norm,roots,maxp=norm_roots(w,lib,131072);J,wroots=positive_integral(c,alpha);q=norm/(1-A*J);history.append(dict(iteration=it,LPobjective=float(p.fun),ratio=q,norm=norm,J=J,norm_roots=len(roots),wing_roots=len(wroots),solver=p.message,warnings=[str(z.message)for z in ww]));print(json.dumps(dict(degree=n,a=alpha,**history[-1])),flush=True);r=q
    cs=[Q(Decimal(str(v)).quantize(Decimal('1e-23')))for v in c];aq=Q(str(alpha));cs[0]=aq/2-sum(((-1)**j)*v for j,v in enumerate(cs)if j)
    packet={'family':'exponential_spectral_laguerre_rational_physical','degree':n,'a':str(aq),'laplace_laguerre_coefficients':list(map(str,cs)),'searched_ratio':q,'status':'EXPLORATORY_UNCERTIFIED'};(a.out/'CANDIDATE.json').write_text(json.dumps(packet,indent=2)+'\n')
    result={'status':'FLOATING_RATIONAL_LAGUERRE_SEARCH_NOT_A_CERTIFICATE_OR_PV','degree':n,'a':alpha,'ratio':q,'norm':norm,'J':J,'norm_roots':roots,'wing_roots':wroots,'history':history,'seconds':time.monotonic()-began,'seed':0,'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'compiler_command':cmd};(a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','degree','a','ratio','seconds']}),flush=True)
if __name__=='__main__':main()
