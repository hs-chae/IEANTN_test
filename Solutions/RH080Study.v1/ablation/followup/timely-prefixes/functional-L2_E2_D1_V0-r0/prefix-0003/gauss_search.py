#!/usr/bin/python3.10
"""FLOAT SEARCH ONLY. Verify generated candidates with gauss_cert.py."""
from math import sqrt,exp,pi,factorial,erf,erfc
import sys,json
from fractions import Fraction
from pathlib import Path
from gauss_cert import transform

def he(jmax):
    P,H=[],[1]; ans=[]
    for n in range(2*jmax+1):
        if not n%2:ans.append([H[k]*2**(k//2) for k in range(0,n+1,2)])
        W=[0]+[2*x for x in H]
        for k,v in enumerate(P):W[k]-=2*n*v
        P,H=H,W
    return ans

def solve(M,v):
    n=len(v); a=[r[:]+[z] for r,z in zip(M,v)]
    for j in range(n):
        i=max(range(j,n),key=lambda k:abs(a[k][j]))
        a[i],a[j]=a[j],a[i]
        aj=a[j]; d=aj[j]
        for k in range(j+1,n):
            ak=a[k]; c=ak[j]/d
            for l in range(j+1,n+1):ak[l]-=aj[l]*c
    u=[0.]*n
    for j in range(n-1,-1,-1):
        u[j]=(a[j][n]-sum(a[j][k]*u[k] for k in range(j+1,n)))/a[j][j]
    return u

n=int(sys.argv[1]); A=float(Fraction(sys.argv[2])); prefix=sys.argv[3]
pol=he(n); norms=[sqrt(2.**(2*j)*factorial(2*j)) for j in range(n+1)]
b0=[p[0]/s for p,s in zip(pol,norms)]
c=[]
if len(sys.argv)>4:
    old=[Fraction(a) for a in json.loads(Path(sys.argv[4]).read_text())]
    assert len(old)<=n+1
    old += [Fraction(0)]*(n+1-len(old))
    for j in range(n,0,-1):
        d=old[j]/pol[j][-1]
        for k,h in enumerate(pol[j]):old[k]-=h*d
        c.append(float(d)*norms[j])
    c.reverse()
else: c=[0.]*n
rs=list(map(sqrt,range(2*n+1)))

def both(x):
    e=exp(-x*x)
    prev=0.;cur=e; R=[]; DP=[]
    xc=2*x
    for k in range(1,2*n+1):
        prev,cur=cur,(xc*cur-rs[k-1]*prev)/rs[k]
        if k%2==0:
            R.append(cur)
            DP.append(2*rs[k]*prev-xc*cur)
    return e,R,DP
def flow(x,mode):
    e,R,D=both(x)
    if mode:
        R=[(-r if j%2==0 else r) for j,r in enumerate(R)]
        D=[(-r if j%2==0 else r) for j,r in enumerate(D)]
    return e,[r-z*e for r,z in zip(R,b0[1:])],[d+2*x*z*e for d,z in zip(D,b0[1:])]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def odd(x):
    p=0.; a=exp(-x*x); arr=[]
    for k in range(1,2*n):
        p,a=a,(2*x*a-rs[k-1]*p)/rs[k]
        if k%2:arr.append(a)
    return arr

def intbasis(a,b,mode):
    E0=sqrt(pi)*.5*((erf(b)-erf(a)) if a<.5 else (erfc(a)-erfc(b)))
    J=E0
    res=[E0]
    for j,(v,w) in enumerate(zip(odd(a),odd(b)),1):
        J=(rs[2*j-1]*J - (w-v))/rs[2*j]
        res.append(((-J if j%2 else J) if mode else J)-b0[j]*E0)
    return res
edge=sqrt(pi)
GR=[]
for mode in range(2):
    left=edge if mode else 0
    right=max(10,2.3*sqrt(n))
    grid=[left+k*(right-left)/1600 for k in range(1601)]
    GR.append([(x,*flow(x,mode)[:2]) for x in grid])

def report(c,w,derivatives=True):
    M=[[0.]*n for j in range(n)]; g=[0.]*n; vals=[]
    for mode,grid in enumerate(GR):
        a,er,R=grid[0]; f=er+dot(c,R); s=f>=0
        roots=[]
        for b,er,R in grid[1:]:
            h=er+dot(c,R)
            if s!=(h>=0):
                l,u=a,b
                for _ in range(41):
                    m=(l+u)/2
                    er,E,_=flow(m,mode)
                    if s==(er+dot(c,E)>=0):l=m
                    else:u=m
                roots.append((l+u)/2)
                s=not s
            a=b
        s=(grid[0][1]+dot(c,grid[0][2]))>=0
        val=0.; start=grid[0][0]
        for r in roots+[grid[-1][0]]:
            if s or not mode:
                i,*z=intbasis(start,r,mode)
                sg=int(s)*2-1
                val+=sg*(i+dot(c,z))
                if derivatives:
                    fac=sg*(w if mode else 1)
                    for j in range(n):g[j]+=fac*z[j]
            if r!=grid[-1][0] and derivatives:
                e,z,d=flow(r,mode)
                fac=(w if mode else 2)/max(1e-40,abs(dot(c,d)-2*r*e))
                for j in range(n):
                    hz=fac*z[j]
                    for k in range(j+1):M[j][k]+=hz*z[k]
            start=r; s=not s
        vals.append(val*2/edge)
    for j in range(n):
        for k in range(j):M[k][j]=M[j][k]
    return vals,g,M

def save(c,filename):
    z=[Fraction(1)]+[Fraction(0)]*n
    for j in range(1,n+1):
        d=Fraction(format(c[j-1]/norms[j],'.25e'))
        for k,h in enumerate(pol[j]):
            if k:z[k]+=h*d
    Path(filename).write_text(json.dumps(list(map(str,z)),indent=2)+'\n')

best=1e100
for it in range(170):
    # Newton direction for mass + r*A*J, updating r (Dinkelbach).
    if it==0:
        (m,j),_,_=report(c,1.,False)
        r=m/(1-A*j)
    (m,j),g,M=report(c,A*r)
    r0=m/(1-A*j)
    if r0<best:
        best=r0
        save(c,prefix+'.json')
    err=max(map(abs,g))
    print(it,n,A,r0,err,flush=True)
    if err<2e-11:break
    c0=c[:]
    for ridge in [1e-5,.002,.05,1.,30.]:
        U=[a[:] for a in M]
        for j in range(n):U[j][j]+=ridge
        u=solve(U,g)
        fac=1.
        for ls in range(34):
            cand=[a-fac*b for a,b in zip(c,u)]
            (mm,jj),_,_=report(cand,0.,False)
            if 1-A*jj>0 and mm/(1-A*jj)<r0-2e-15:
                c=cand; r=mm/(1-A*jj); break
            fac/=2
        else: continue
        break
    if c==c0:break
