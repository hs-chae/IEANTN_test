"""Exact rational certificates for the analytic Ramanujan bounds."""
from fractions import Fraction as Q
from math import factorial as fac, comb
from functools import lru_cache
from subprocess import check_output

eL=Q(2718281828459045235,10**18)
eU=eL+Q(1,10**18)
c=Q(397888,10**7)
q=Q(1048,10**15)
d=Q(5,32)
beta=1-d
A=Q(1,64)
def series(t,n):
    s=v=Q(1)
    for i in range(1,n+1):
        v=v*t/i
        s+=v
    return s,s+v*t/(n+1)/(1-t/(n+2))
assert series(Q(1),25)[0]>eL and series(Q(1),25)[1]<eU

@lru_cache(None)
def expb(t):
    t=Q(t)
    if t<0:
        l,r=expb(-t)
        return 1/r,1/l
    m=t//1
    l,r=series(t-m,18)
    return eL**m*l,eU**m*r
def eu(t):return expb(t)[1]
def el(t):return expb(t)[0]

def logb(x):
    assert x>=1
    k=0
    while x>=2:
        k+=1;x/=2
    def at(t):
        z=(t-1)/(t+1)
        s=2*sum(z**(2*j+1)/(2*j+1) for j in range(50))
        return s,s+2*z**101/(101*(1-z*z))
    a,b=at(Q(2))
    g,h=at(x)
    return k*a+g,k*b+h

def alt(t,n):
    v=sum((-1)**j*t**(2*j+1)/(2*j+1) for j in range(n))
    w=v+(-1)**n*t**(2*n+1)/(2*n+1)
    return min(v,w),max(v,w)
# Machin's formula follows by the tangent addition law in the first quadrant.
pl=16*alt(Q(1,5),12)[0]-4*alt(Q(1,239),6)[1]
pu=16*alt(Q(1,5),12)[1]-4*alt(Q(1,239),6)[0]
assert 1/(8*pl)<c and pu/(3*10**12)<q
def H(u):return sum(Q(fac(i))/u**i for i in range(21))
def V(u):return 4*u*eu(-u)+12*Q(fac(21))/u**21
def h0(u):return q+117*eu(-u/2)
def m0(u):return (q*20/19+260*eu(-u/2))/u+Q(16,5)*u*eu(20-u)
def E1(u):return ((A*u*u+A*u/beta)*eu(-d*u)
                +(3+Q(20,3)/u)*eu(-u/2)
                +(u/220)*eu(220-u)*m0(Q(220)))
def E(a,b):
    l=[]
    if b<=58:l.append(c*a*a*eu(-a/2))
    if a>=40:l.append(h0(a)+m0(a))
    if a>=220:l.append(E1(a))
    return min(l)

def li_anchor():
    u=Q(24); n=120
    s=sum(u**k/Q(k*fac(k)) for k in range(1,n+1))
    t=u**(n+1)/Q((n+1)*fac(n+1))/(1-u/(n+2))
    l,r=logb(u)
    assert s+l-eu(u)*H(u)/u>0
    assert s+t+r+1-el(u)*H(u)/u<4

S=[sum(fac(i)*fac(k-i) for i in range(max(0,k-20),min(k,20)+1))
   for k in range(41)]
C=[sum(comb(k,j)*fac(j) for j in range(k+1))-S[k] for k in range(21)]
assert C[:7]==[0,0,0,0,1,14,145] and min(C[4:])>0
def mainlower(a,b):
    return (sum(Q(C[k])*b**(4-k) for k in range(4,21))
           -sum(Q(S[k])*a**(4-k) for k in range(21,41)))
def loss(a,b,signed):
    # In the finite RH subrange, compute the shifted cost normalized
    # by L^4 directly, so that monotonicity avoids interval inflation.
    sh=(c*a**5*(a-1)*eu(-(a-1)/2) if b-1<=58 else
        b**4*a/(a-1)*E(a-1,b-1))
    ep=V(a)+(0 if signed else E(a,b))
    return sh+b**4*ep*(2*H(a)+ep)
def lossmin(a,b,signed):
    ep=V(a)+(0 if signed else E(a,b))
    return min(loss(a,b,signed),
               b**4*a/(a-1)*E(a-1,b-1)+b**4*ep*(2*H(a)+ep))
def certificates():
    assert eu(Q('36.98'))<Q('1.15e16')
    assert eu(Q(43))<10**19
    assert eu(Q(58))<Q('2.169e25')
    li_anchor()
    steps=[Q('36.98'),Q('36.981'),Q(37),Q('37.1'),Q(38),Q(39),Q(40),Q(41),Q(42),Q(43)]
    for a,b in zip(steps,steps[1:]):
        assert mainlower(a,b)-lossmin(a,b,True)>Q(1,50000),(a,b)
    for a in range(43,48):
        a=Q(a);b=a+1
        assert mainlower(a,b)-lossmin(a,b,False)>Q(1,50000),(a,b)
    # Need 1+13/L, not 1+13/a after bounding the entire constant polynomial:
    # write J-1-13/L as 1/L+145/L²+...
    for a in range(48,225):
        a=Q(a);b=a+1
        assert mainlower(a,b)-Q(13,b)-lossmin(a,b,False)>1,(a,b)
    # For L>=225 the negative square coefficients above degree 20
    # are absorbed by c_6/L^2 (rescaled).
    a=Q(225)
    assert sum(Q(S[k])*a**(6-k) for k in range(21,41))<145
    assert a**5*(a/(a-1)*E1(a-1)+(V(a)+E1(a))*(2*H(a)+V(a)+E1(a)))<1

def endpoint(bin):
    x=38358837682
    y=14111427770
    assert eU*y<x and x+1<eL*(y+1)
    from math import isqrt
    assert any((x+1)%p==0 for p in range(2,isqrt(x+1)+1))
    out=check_output([bin],input=f"{x}\n{x+1}\n{y}\n".encode()).split()
    assert list(map(int,out))==[x,1644673232,x+1,1644673232,y,632207037]
    a,b=1644673232,632207037
    l=Q('38358837682.217');r=Q('38358837682.219')
    assert eU*l*b/logb(l)[0] < a*a < eL*r*b/logb(r)[1]

if __name__=='__main__':
    import sys
    certificates()
    if len(sys.argv)==2:endpoint(sys.argv[1])
    print("analytic and requested endpoint certificates OK")
