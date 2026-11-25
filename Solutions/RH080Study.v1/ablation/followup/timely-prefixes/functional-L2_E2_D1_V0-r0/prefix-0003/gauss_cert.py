#!/usr/bin/python3.10
"""Exact-arithmetic certificate for even polynomial-Gaussian functions."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from functools import lru_cache
import json,sys

def value(cs,x):
    y=0
    for c in reversed(cs):
        y=y*x+c
    return y

def transform(cs):
    # (-1)^j H_{2j}(x)/4^j, H_{n+1}=2x H_n-2n H_{n-1}.
    H,previous=[1],[]
    out=[Q(0)]*len(cs)
    for n in range(2*len(cs)-1):
        if n%2==0:
            j=n//2
            for k in range(j+1):
                out[k]+=cs[j]*H[2*k]*Q((-1)**j,4**j)
        shifted=[0]+[2*c for c in H]
        for i,h in enumerate(previous): shifted[i]-=2*n*h
        H,previous=shifted,H
    return out

def atan_series(inv,n=110):
    v=sum((Q((-1)**i,(2*i+1)*inv**(2*i+1)) for i in range(n)),Q(0))
    d=Q((-1)**n,(2*n+1)*inv**(2*n+1))
    return min(v,v+d),max(v,v+d)
def pi_bounds():
    a,b=atan_series(5); c,d=atan_series(239)
    return 16*a-4*d,16*b-4*c
def sqrt_bounds(a,b,scale=10**75):
    assert 0<=a<=b
    lo=isqrt((a*scale**2).__floor__())
    hi=isqrt((b*scale**2).__floor__())+1
    return Q(lo,scale),Q(hi,scale)
SP=sqrt_bounds(*pi_bounds())
S=10**125
def down(x):return (S*x).__floor__()
def up(x):return (S*x).__ceil__()

@lru_cache(maxsize=None)
def e_and_erfint(x):
    # Returns integer endpoints at scale S. n is checked by the first omitted
    # integral/exp Lagrange bound. At r=0 both terms exact.
    assert 0<=x<=20
    a=x*x
    termlo=termhi=S
    elo=ehi=S
    ilo,ihi=down(x),up(x)
    for n in range(1,4000):
        termlo=(termlo*a/n).__floor__()
        termhi=(termhi*a/n).__ceil__()
        if termhi<=min(4000,n+1) and n>a:
            # ceil-rounded term may get stuck, but still uniformly bounds error.
            b=(termhi*x/(2*n+1)).__ceil__()
            return (Q(elo-termhi,S),Q(ehi+termhi,S)),(Q(ilo-b,S),Q(ihi+b,S))
        ilo1=(termlo*x/(2*n+1)).__floor__()
        ihi1=(termhi*x/(2*n+1)).__ceil__()
        if n%2: elo-=termhi; ehi-=termlo; ilo-=ihi1; ihi-=ilo1
        else: elo+=termlo; ehi+=termhi; ilo+=ilo1; ihi+=ihi1
    raise ValueError('increase series budget')

def mulscalar(c,iv):
    a,b=iv
    return (c*a,c*b) if c>=0 else (c*b,c*a)
def add(a,b):return a[0]+b[0],a[1]+b[1]

def primitive(cs):
    # I_j(x)=((2j-1)I_{j-1}(x)-x^{2j-1}e^{-x^2})/2
    a=list(cs)
    r=[Q(0)]*(len(a)-1)
    for j in range(len(a)-1,0,-1):
        r[j-1]=-a[j]/2
        a[j-1]+=(2*j-1)*a[j]/2
    cache={}
    def f(x):
        if x is None:
            return mulscalar(a[0]/2,SP)
        if x not in cache:
            e,i=e_and_erfint(x)
            cache[x]=add(mulscalar(a[0],i),mulscalar(x*value(r,x*x),e))
        return cache[x]
    return f

def intervals(cs,grid=256):
    # Fast attempt: rational signs. Succeeds only if all positive roots found.
    # Squared-variable degree bounds the total count including multiplicities.
    assert cs[0]!=0 and cs[-1]!=0
    poss=[]
    a=Q(0); fa=cs[0]
    for k in range(1,grid*20+1):
        b=Q(k,grid); fb=value(cs,b*b)
        if not fb: continue
        if fa*fb<0:poss.append((a,b,fa>0))
        a,fa=b,fb
        if len(poss)==len(cs)-1: break
    if len(poss)<len(cs)-1:
        # Exact fallback: Sturm/continued-fraction isolation on the squared
        # variable. SymPy is used only here. An independent rational sign and
        # Sturm count validates any fallback isolator.
        import sympy as sp
        X=sp.Symbol('z')
        poly=sp.Poly.from_list(list(reversed(cs)),X,domain=sp.QQ)
        assert poly.gcd(poly.diff()).degree()==0, 'certificate expects simple roots'
        poss=[]
        for (l,h),m in poly.intervals(eps=sp.Rational(1,10**30),inf=0):
            assert m==1 and 0<l<=h
            lo,hi=sqrt_bounds(Q(l),Q(h),10**36)
            lo=max(Q(0),lo-Q(1,10**36)); hi+=Q(1,10**36)
            va,vb=value(cs,lo*lo),value(cs,hi*hi)
            assert va*vb<0
            poss.append((lo,hi,va>0))
        assert all(poss[k][1]<poss[k+1][0] for k in range(len(poss)-1))
        st=poly.sturm()
        def changes(v):
            s=[z>0 for z in v if z]
            return sum(a!=b for a,b in zip(s,s[1:]))
        assert len(poss)==changes([p.eval(0) for p in st])-changes([p.LC() for p in st])
    out=[]
    for a,b,sgn in poss:
        for _ in range(112):
            mid=(a+b)/2
            f=value(cs,mid*mid)
            if f==0:
                a=b=mid
                break
            if (f>0)==sgn:a=mid
            else:b=mid
            if b-a<Q(1,10**34):break
        out.append((a,b))
    return out

def integral(cs,positive,l):
    f=primitive(cs)
    lo=hi=Q(0)
    sign=value(cs,l*l)>0
    def accum(a,b,sign):
        fa,fb=f(a),f(b)
        J=(fb[0]-fa[1],fb[1]-fa[0])
        return J if sign else ((0,0) if positive else (-J[1],-J[0]))
    for a,b in intervals(cs):
        if b<=l:continue
        assert l<a
        i,j=accum(l,a,sign)
        lo+=i
        hi+=j+(b-a)*value(list(map(abs,cs)),b*b)
        l=b
        sign=not sign
    i,j=accum(l,None,sign)
    lo+=i;hi+=j
    assert 0<=lo<=hi
    return 2*lo/SP[1],2*hi/SP[0]
def enclosure(cs):
    qs=transform(cs)
    lo=integral(qs,True,SP[1])[0]
    hi=integral(qs,True,SP[0])[1]
    return integral(cs,False,Q(0)),(lo,hi)

def decimals(a,d=16):
    return (a*10**d).__floor__(),(a*10**d).__ceil__()
def run(path,A,target=None):
    cs=list(map(Q,json.loads(Path(path).read_text())))
    m,j=enclosure(cs)
    assert A>=0 and cs[0]-A*j[1]>0
    r=m[1]/(cs[0]-A*j[1])
    print(path,'(decimals scaled by 10^16)','mass upper:',decimals(m[1])[1], 'leak upper:',decimals(j[1])[1], 'R upper:',decimals(r)[1],flush=True)
    if target is not None:
        assert r<target
        print('PROVED R <',target,flush=True)
    critical=(cs[0]-Q(5,4)*m[1])/j[1]
    print('Conservative penalty for R <= 4/5 (scaled by 10^16):',decimals(critical)[0],flush=True)
    return r,critical

if __name__=='__main__':
    run(sys.argv[1],Q(sys.argv[2]) if len(sys.argv)>2 else Q(36,11),Q(sys.argv[3]) if len(sys.argv)>3 else None)
