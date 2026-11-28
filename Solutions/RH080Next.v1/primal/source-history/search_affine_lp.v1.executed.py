#!/usr/bin/env python3
"""Compact spectral-hat LP search; floating norm review, not a proof or PV."""
import argparse,ctypes,hashlib,json,math,os,subprocess,sys,time,warnings
from decimal import Decimal,ROUND_HALF_EVEN
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import scipy
from scipy import fft,optimize,sparse
A=36/11
def need(v,m):
    if not v:raise ValueError(m)
def area(l,r):
    if l>=0 and r>=0:return(l+r)/2
    if l<=0 and r<=0:return Q(0)
    return max(l,r)**2/(2*abs(l-r))
def exact_data(m,ints,scale):
    w=[Q(x,scale)for x in ints]+[Q(0)]
    J=2*sum((area(w[j],w[j+1])for j in range(m,len(w)-1)),Q(0))/m
    F0=(w[0]+2*sum(w[1:]))/m
    return F0,J
def evaluator(source,out):
    target=out/'floating_trig.so';cmd=['cc','-std=c11','-O3','-fPIC','-shared',str(source),'-o',str(target),'-lm'];subprocess.run(cmd,check=True,capture_output=True)
    lib=ctypes.CDLL(str(target));vp=np.ctypeslib.ndpointer(dtype=np.float64,ndim=1,flags='C_CONTIGUOUS')
    for name in ['trig_value','trig_primitive']:
        fn=getattr(lib,name);fn.argtypes=[ctypes.c_size_t,vp,ctypes.c_longdouble];fn.restype=ctypes.c_longdouble
    return lib,cmd
def norm_roots(w,lib,grid):
    n=len(w);N=grid;tmp=np.zeros(N);tmp[0]=w[0];tmp[1:n]=w[1:]
    values=fft.dct(tmp,type=3,norm=None);ys=(np.arange(N)+.5)/(2*N)
    def f(y):return float(lib.trig_value(n,w,y))
    def prim(y):return float(lib.trig_primitive(n,w,y))
    roots=[]
    # Actual cosseries at endpoints brackets the first/last half-cell too.
    ys=np.r_[0.,ys,.5];values=np.r_[f(0.),values,f(.5)]
    for i in np.flatnonzero(values[:-1]*values[1:]<0):
        r=optimize.brentq(f,ys[i],ys[i+1],xtol=8e-16,rtol=1e-14)
        if not roots or r-roots[-1]>1e-12:roots.append(r)
    ends=[0.]+roots+[.5];total=0.
    for a,b in zip(ends,ends[1:]):total+=(1 if f((a+b)/2)>=0 else-1)*(prim(b)-prim(a))
    return 2*total,roots,float(np.max(abs(values)))
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--m',type=int,required=True);ap.add_argument('--radius',type=int,default=7);ap.add_argument('--grid',type=int,default=8192);ap.add_argument('--review-grid',type=int,default=131072);ap.add_argument('--A',type=float,default=A);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--threads',type=int,default=2);a=ap.parse_args()
    need(not a.out.exists(),'Fresh output');a.out.mkdir(parents=True);began=time.monotonic();m=a.m;n=m*a.radius;N=a.grid
    need(N>=4*n,'At leastfour quadraturenodes perhighestmode');src=Path(__file__);lib,cmd=evaluator(src.with_name('floating_trig.c'),a.out)
    theta=math.pi*(np.arange(N)+.5)/N;B=2*np.cos(theta[:,None]*np.arange(n)[None,:]);B[:,0]=1.
    M=n-m;Jmat=sparse.csr_matrix((np.ones(M),(np.arange(M),m+np.arange(M))),shape=(M,n))
    bc=sparse.csr_matrix(B);Aub=sparse.vstack([sparse.hstack([bc,-sparse.eye(N),sparse.csr_matrix((N,M))]),sparse.hstack([-bc,-sparse.eye(N),sparse.csr_matrix((N,M))]),sparse.hstack([Jmat,sparse.csr_matrix((M,N)),-sparse.eye(M)])],format='csr')
    eq=np.r_[np.r_[1.,np.full(n-1,2.)]/m,np.zeros(N+M)][None,:];r=.83394544;history=[]
    for it in range(3):
        jweights=np.full(M,2/m);jweights[0]=1/m
        cost=np.r_[np.zeros(n),np.full(N,1/N),r*a.A*jweights]
        with warnings.catch_warnings(record=True)as ww:
            p=optimize.linprog(cost,A_ub=Aub,b_ub=np.zeros(2*N+M),A_eq=sparse.csr_matrix(eq),b_eq=[1.],bounds=[(None,None)]*n+[(0,None)]*(N+M),method='highs-ipm',options={'threads':a.threads,'random_seed':0,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-11})
        need(p.success,p.message);w=np.ascontiguousarray(p.x[:n]);w/=float(eq[0,:n]@w)
        scale=10**18;ints=[int((Decimal(str(x))*scale).to_integral_value(rounding=ROUND_HALF_EVEN))for x in w];ints[0]=m*scale-2*sum(ints[1:]);w=np.ascontiguousarray([float(Q(x,scale))for x in ints]);F0,J=exact_data(m,ints,scale)
        norm,roots,maxp=norm_roots(w,lib,max(a.review_grid,16*n));q=norm/(float(F0)-a.A*float(J));history.append(dict(iteration=it,LPobjective=float(p.fun),ratio=q,norm=norm,J=float(J),F0=str(F0),roots=len(roots),maxP=maxp,solver=p.message,warnings=[str(z.message)for z in ww]));print(json.dumps(dict(m=m,radius=a.radius,**history[-1])),flush=True);r=q
    packet={'m':m,'scale':scale,'coefficients':ints};(a.out/'CANDIDATE.json').write_text(json.dumps(packet,indent=2)+'\n')
    result={'status':'FLOATING_AFFINE_LP_ROOT_REVIEW_NOT_CERTIFICATE_OR_PV','m':m,'radius':a.radius,'grid':N,'review_grid':max(a.review_grid,16*n),'A':a.A,'ratio':q,'norm':norm,'F0':str(F0),'J_exact':str(J),'roots':roots,'history':history,'seconds':time.monotonic()-began,'seed':0,'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,'compiler_command':cmd,'floating_helper_sha256':hashlib.sha256(src.with_name('floating_trig.c').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()};(a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','m','radius','ratio','seconds']}),flush=True)
if __name__=='__main__':main()
