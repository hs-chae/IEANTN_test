#!/usr/bin/env python3
"""Deterministic floating Gaussian-Hermite search; NOT proof acceptance or PV.

The even Hermite coordinate has Fourier eigenvalue(-1)^j. Normalize F(0)=1.
After smoothed Newton initialization, use exact sign-root intervals with analytic
Hermite antiderivatives, avoiding a quadrature-grid objective at the final step.
Every exported candidate still needs independent rigorous certification and Lean.
"""
import argparse,hashlib,json,math,os,sys,time
from decimal import Decimal,localcontext
from fractions import Fraction
from pathlib import Path
import numpy as np
import scipy
from scipy import optimize,special,linalg

SQ=math.sqrt(math.pi);A=36/11
def need(v,m):
    if not v:raise ValueError(m)
def hm(x,n,full=False):
    x=np.atleast_1d(x).astype(np.longdouble)
    z=np.exp(-x*x);out=[np.array(z,dtype=float)];w=2*x*z
    if full:out.append(np.array(w,dtype=float))
    for j in range(2,2*n+2):
        z,w=w,(2*x*w-math.sqrt(j-1)*z)/math.sqrt(j)
        if full or j%2==0:out.append(np.array(w,dtype=float))
    return np.array(out).T
def vals0(n):return hm([0.],n)[0]
def anti(x,n):
    if math.isinf(x):h=np.zeros(2*n+2);base=SQ/2
    else:h=hm([x],n,True)[0];base=SQ/2*special.erf(x)
    out=[base]
    for j in range(1,n+1):out.append((math.sqrt(2*j-1)*out[-1]-h[2*j-1])/math.sqrt(2*j))
    return np.array(out)
def coefficients(free):
    v=vals0(len(free));return np.r_[1-v[1:]@free,free]
def initial_from_laguerre(path,n):
    if path is None:return np.zeros(n)
    raw=json.loads(Path(path).read_text());c=[float(Fraction(v))for v in raw['coefficients_decimal_exact_rationals']]
    out=np.zeros(n+1)
    for j,x in enumerate(c[:n+1]):out[j]=(-1)**j*x*math.exp(.5*special.gammaln(2*j+1)-j*math.log(2)-special.gammaln(j+1))
    return out[1:]/(vals0(n)@out)
def smooth_rows(n,s,dx):
    end=max(14.,math.sqrt(4*n)+5)
    rows=[];weights=[];wing=[];v=vals0(n)
    for start,mult,iw in [(0.,1/s,False),(SQ/s,1.,True)]:
        count=math.ceil((end-start)/dx);step=(end-start)/count;x=start+step*(np.arange(count)+.5)
        b=hm(x,n)
        if iw:b=b*((-1.)**np.arange(n+1))
        rows.append(b);weights.extend([2*step/SQ*mult]*count);wing.extend([iw]*count)
    b=np.vstack(rows);return b[:,0],b[:,1:]-b[:,0,None]*v[None,1:],np.array(weights),np.array(wing)
def smooth_value(free,eps,base,b,w,wing,r,hessian):
    z=base+b@free;q=np.sqrt(z*z+eps*eps);ww=w*np.where(wing,r*A/2,1.)
    val=float(ww@(q+np.where(wing,z,0.)))
    if not hessian:return val
    g=b.T@(ww*(z/q+wing));d=ww*eps*eps/q**3
    H=b.T@(d[:,None]*b)
    return val,g,H
def smooth_newton(free,s,r,phases):
    log=[];n=len(free)
    for eps,dx,iters in phases:
        base,b,w,wing=smooth_rows(n,s,dx)
        for it in range(iters):
            value,g,H=smooth_value(free,eps,base,b,w,wing,r,True)
            e,v=linalg.eigh(H,check_finite=False);floor=max(e[-1]*1e-12,1e-12)
            direction=v@((v.T@g)/np.maximum(e,floor));alpha=1.
            while alpha>2**-25:
                trial=free-alpha*direction;val=smooth_value(trial,eps,base,b,w,wing,r,False)
                if val<value:free=trial;break
                alpha/=2
            if alpha<=2**-25 or np.max(np.abs(alpha*direction))<2e-10:break
        log.append(dict(eps=eps,dx=dx,iterations=it+1,value=value,gradient=float(np.max(np.abs(g)))))
        print(json.dumps(dict(stage='smooth',degree=n,scale=s,**log[-1])),flush=True)
    return free,log
def root_integrals(c,n,start,end,grid,positive):
    zz=grid@c;xs=np.linspace(start,end,len(zz));roots=[]
    def value(x):return float(hm([x],n)[0]@c)
    for i in np.flatnonzero(zz[:-1]*zz[1:]<0):
        root=optimize.brentq(value,xs[i],xs[i+1],xtol=4e-15,rtol=1e-14)
        if not roots or root-roots[-1]>1e-10:roots.append(root)
    ends=[start]+roots+[math.inf];I=np.zeros(n+1)
    for a,b in zip(ends,ends[1:]):
        middle=(a+b)/2 if math.isfinite(b)else max(a+1.,end)
        sign=1. if value(middle)>=0 else -1.
        if positive and sign<0:continue
        I+=(1. if positive else sign)*(anti(b,n)-anti(a,n))
    if roots:
        h=hm(roots,n,True);even=h[:,::2][:,:n+1]
        deriv=np.array([math.sqrt(2*j)*h[:,2*j-1]-(math.sqrt(2*j+1)*h[:,2*j+1])if j else-h[:,1]for j in range(n+1)]).T@c
        rr=np.array(roots);need(np.all(np.abs(deriv)>0),'Multiple root: use nonsmooth method')
    else:even=np.zeros((0,n+1));deriv=np.zeros(0)
    return I,even,np.abs(deriv),roots
def exact_objective(free,s,r,grids=None):
    n=len(free);c=coefficients(free);v=vals0(n);signs=(-1.)**np.arange(n+1);end=max(14.,math.sqrt(4*n)+5)
    if grids is None:
        grids=[hm(np.linspace(start,end,math.ceil((end-start)/.005)+1),n)for start in [0.,SQ/s]]
    total=0.;gradient=np.zeros(n);H=np.zeros((n,n));values={};rootsets={}
    for iw,start,mult,basis in [(False,0.,1/s,grids[0]),(True,SQ/s,r*A,grids[1])]:
        cc=c*signs if iw else c;I,B,d,roots=root_integrals(cc,n,start,end,basis,iw)
        integ=float(I@cc)*2/SQ;values['J'if iw else'N']=integ if iw else integ/s;rootsets['wing'if iw else'norm']=roots
        if iw:I=I*signs;B=B*signs
        total+=mult*integ;gradient+=mult*2/SQ*(I[1:]-v[1:]*I[0])
        if len(B):
            Z=B[:,1:]-B[:,0,None]*v[None,1:]
            H+=mult*2/SQ*(1 if iw else 2)*(Z.T@(Z/d[:,None]))
    return total,gradient,H,values,rootsets,grids
def root_newton(free,s,r,iterations):
    history=[];grids=None
    for it in range(iterations):
        value,g,H,data,roots,grids=exact_objective(free,s,r,grids)
        e,v=linalg.eigh(H,check_finite=False);floor=max(e[-1]*1e-10,1e-9)
        direction=v@((v.T@g)/np.maximum(e,floor));alpha=1.
        for back in range(30):
            trial=free-alpha*direction;vv=exact_objective(trial,s,r,grids)[0]
            if vv<value-1e-15:free=trial;break
            alpha/=2
        history.append(dict(iteration=it,value=value,q=data['N']/(1-A*data['J']),gradient=float(np.max(abs(g))),alpha=alpha))
        if it%4==0:print(json.dumps(dict(stage='roots',degree=len(free),scale=s,**history[-1])),flush=True)
        if alpha<2**-25 or np.max(abs(alpha*direction))<1e-11:break
    return free,history
def candidate(free):
    c=coefficients(free)
    with localcontext()as ctx:
        ctx.prec=100;out=[]
        for j,v in enumerate(c):
            z=Decimal(str(v))*Decimal(2**j)*Decimal(math.factorial(j))/Decimal(math.factorial(2*j)).sqrt()*((-1)**j)
            out.append(Fraction(z))
        # Exact rational normalization F(0)=1 in the Laguerre coordinate.
        f0=sum(v*Fraction(math.factorial(2*j),4**j*math.factorial(j)**2)for j,v in enumerate(out));out=[v/f0 for v in out]
    return dict(degree=len(free),physical_degree=2*len(free),coefficients_decimal_exact_rationals=list(map(str,out)),source='New campaign deterministic Gaussian-Hermite continuous sign-root optimization; NOT certified')
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--degree',type=int,required=True);ap.add_argument('--scale',type=float,default=1.);ap.add_argument('--start',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--quick',action='store_true');a=ap.parse_args()
    need(not a.out.exists(),'Fresh output directory');a.out.mkdir(parents=True);start=time.monotonic();free=initial_from_laguerre(a.start,a.degree)
    phases=[(1e-3,.02,12),(1e-4,.01,12),(1e-5,.005,16),(1e-6,.0025,18)]
    if not a.quick:phases +=[(1e-7,.00125,18),(1e-8,.000625,20)]
    free,sm=smooth_newton(free,a.scale,.83394544,phases);free,ro=root_newton(free,a.scale,.83394544,24 if a.quick else 60)
    value,g,H,data,roots,_=exact_objective(free,a.scale,.83394544);q=data['N']/(1-A*data['J']);packet=candidate(free);packet.update(scale=a.scale,searched_ratio=q)
    (a.out/'CANDIDATE.json').write_text(json.dumps(packet,indent=2)+'\n');(a.out/'HERMITE.json').write_text(json.dumps(list(map(float,coefficients(free)))))
    result=dict(status='FLOATING_CONTINUOUS_ROOT_SEARCH_NOT_A_CERTIFICATE',degree=a.degree,scale=a.scale,ratio=q,data=data,roots=roots,smoothing=sm,root_newton=ro,seconds=time.monotonic()-start,seed=None,python=sys.version,numpy=np.__version__,scipy=scipy.__version__,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','degree','scale','ratio','seconds']}),flush=True)
if __name__=='__main__':main()
