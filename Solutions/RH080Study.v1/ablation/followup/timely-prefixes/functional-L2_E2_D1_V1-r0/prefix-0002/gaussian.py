#!/usr/bin/python3.10
"""Exact rational sign isolation and Gaussian integrals. See candidate.md."""
import argparse,json,re
from math import factorial,isqrt
from fractions import Fraction as Q
from pathlib import Path
from check import PL,PU,need,up

def trim(a):
    while a and not a[-1]: a.pop()
    return a

def val(a,x):
    v=0
    for k in a[::-1]: v=v*x+k
    return v

def rem(a,b):
    a=a.copy()
    while len(a)>=len(b):
        d=len(a)-len(b)
        u=a[-1]/b[-1]
        for i,v in enumerate(b): a[i+d]-=u*v
        trim(a)
    return a

def primitive_int(a):
    """Positive rescaling of a rational polynomial to primitive integers."""
    from math import gcd,lcm
    d=lcm(*(x.denominator for x in a))
    b=[int(d*x) for x in a]
    g=gcd(*b)
    return [Q(x//g) for x in b]

def sturm(a):
    s=[primitive_int(a),primitive_int([j*x for j,x in enumerate(a) if j])]
    while len(s[-1])>1:
        r=rem(s[-2],s[-1])
        need(bool(r),"multiple roots")
        s.append(primitive_int([-v for v in r]))
    return s

def sign(x): return (x>0)-(x<0)
def vr(s,t=None):
    ns=[sign(a[-1] if t is None else val(a,t)) for a in s]
    nz=[a for a in ns if a]
    return sum(a!=b for a,b in zip(nz,nz[1:]))

def isolate(a):
    s=sturm(a); lo,hi=Q(0),Q(1)
    n=vr(s,lo); inf=vr(s)
    need(a[0]!=0, "zero endpoint")
    while vr(s,hi)>inf or val(a,hi)==0:hi*=2
    stack=[(lo,hi,n,inf)]; out=[]
    while stack:
        l,h,q,r=stack.pop()
        if q==r:continue
        if h-l<Q(1,2**94):
            need(q-r==1, "unseparated roots")
            out.append((l,h));continue
        m=(l+h)/2
        while val(a,m)==0:m=(2*l+m)/3
        v=vr(s,m)
        stack.extend([(m,h,v,r),(l,m,q,v)])
    return out

def sqrt_bounds(l,h):
    D=10**29
    def low(x):return isqrt((x.numerator*D**2)//x.denominator)
    return Q(low(l),D),Q(low(h)+1,D)

def c_and_R(a):
    """P(t)=c + R(t)+2t R'(t) - 2tR(t)."""
    R=[Q(0)]*(len(a)-1)
    b=Q(0)
    for j in range(len(a)-1,0,-1):
        b=((2*j+1)*b-a[j])/2
        R[j-1]=b
    return a[0]-R[0],R

def exp_primitive(a,c,R,l,h):
    u=(l+h)/2;t=u*u
    # Both Taylor sums through n-1, bound e^(-z) remainder by z^n/n!.
    n=240
    e=Q(1); E=Q(1); H=Q(1)
    for i in range(1,n):
        e *= -t/i
        E += e
        H += e/(2*i+1)
    R0=val(R,t)
    center=u*(c*H+R0*E)
    et=t**n/factorial(n)
    radius=u*et*(abs(c)/ (2*n+1)+abs(R0))
    radius+=(h-l)/2 * val(list(map(abs,a)),h*h)
    return center-radius,center+radius

def plus(x,y):return (x[0]+y[0], x[1]+y[1])
def minus(x,y):return (x[0]-y[1],x[1]-y[0])
def scl(c,x):return (c*x[0],c*x[1]) if c>=0 else (c*x[1],c*x[0])
def mul(x,y):
    ps=[u*v for u in x for v in y]
    return min(ps),max(ps)

def integrals(a,wing):
    c,R=c_and_R(a)
    ar=sqrt_bounds(PL,PU)
    if wing:
        ends=[ar]
    else:
        ends=[(Q(0),Q(0))]
    for rl,rh in isolate(a):
        if wing:
            if rh<PL:continue
            need(rl>PU,"root meets wing endpoint")
        ends.append(sqrt_bounds(rl,rh))
    vals=[exp_primitive(a,c,R,l,h) for l,h in ends]
    factor=2/ar[1],2/ar[0]
    # Physical integrals scaled by 2/sqrt(pi); the primitive at infinity
    # has scaled value c exactly (uR(u^2)e^(-u^2) vanishes).
    scaled=[mul(v,factor) for v in vals]+[(c,c)]
    neg=(Q(0),Q(0))
    for k,(x,y) in enumerate(zip(scaled,scaled[1:])):
        l=ends[k][1]
        probe=(l+ends[k+1][0])/2 if k+1<len(ends) else l+1
        need(val(a,probe*probe)!=0,"probe zero")
        if val(a,probe*probe)<0:
            neg=plus(neg,minus(y,x))
    return minus(minus((c,c),scaled[0]),scl(1 if wing else 2,neg))

def baseline():
    lines=Path('/representation/source/GaussianSources.lean').read_text().splitlines()
    P=[Q(x) for x in re.findall(r'(-?\d+/\d+) :',lines[4])][::2]
    G=[Q(x) for x in re.findall(r'(-?\d+/\d+) :',lines[5])][::2]
    need(len(P)==len(G)==13,"source coefficients")
    return P,G

def pair(path):
    # Location basis u=sqrt(pi)*x, physicists' H_(2k)(sqrt(2)*u).
    # Eigenvalue (-1)^k with the stated Fourier convention.
    coeff=[Q(x) for x in json.loads(Path(path).read_text())]
    prev=[];cur=[Q(1)]
    P=[Q(0)]*len(coeff); G=P.copy()
    for k,v in enumerate(coeff):
        for j,t in enumerate(cur):
            P[j]+=v*t
            G[j]+=(-1)**k*v*t
        # H_(2k+2) = (8u²-2(4k+1))*H_(2k)-4(2k)(2k-1)*H_(2k-2).
        nxt=[Q(0)]*(len(cur)+1)
        for j,t in enumerate(cur):
            nxt[j]-=2*(4*k+1)*t
            nxt[j+1]+=8*t
        for j,t in enumerate(prev):
            nxt[j]-=4*(2*k)*(2*k-1)*t
        prev,cur=cur,nxt
    return trim(P),trim(G)

def verify(A,target,path):
    P,G=baseline() if path=='baseline' else pair(path)
    M=integrals(P,False)[1]
    J=integrals(G,True)[1]
    D=P[0]-A*J
    need(P[0]>0 and J>=0 and D>0,"positive data")
    print("norm <=",up(M),"leak <=",up(J),flush=True)
    if J>0:
        print("penalty sufficient at .8 >",up((P[0]-Q(5,4)*M)/J-Q(1,10**15)),flush=True)
    print("ratio <=",up(M/D),flush=True)
    need(M/D<target,"target failed")
    print("PASS exact arithmetic")
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument("path");p.add_argument("A",type=Q);p.add_argument("target",type=Q)
    a=p.parse_args()
    verify(a.A,a.target,a.path)
