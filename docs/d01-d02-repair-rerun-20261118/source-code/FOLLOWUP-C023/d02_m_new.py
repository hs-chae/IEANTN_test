"""Directed comparisons for the Mertens/weighted-prime-sum consequences."""
from fractions import Fraction as Q
from d02_density_new import D,D0,H,q,CT,F,J,eu,el,mass
from functools import lru_cache

@lru_cache(None)
def E(L,d=D,mode='min'):
    # max(L |D1|, L |Z_Q|, |D2|)
    k=1+1/L
    Z=eu(-L/2)
    X=eu(-L)
    cap=q+CT*Z
    if mode!='plateau':
        f=F(L,d)*eu(-d*L)
        cap=min(cap,f) if mode=='min' else f
    return (cap+(1+Q('.0003')+Q('.048')*k)*Z
            +k*(Q('2.67')*eu(-2*L/3)
                +(1+Q(4,H)/L)*J(L,d)*eu(-d*L)+2*X)
            +Q('.502')*X)
@lru_cache(None)
def U(L,d=D):
    k=1+1/L
    B=(F(L,d)+(1+Q('.0003')+Q('.048')*k)*eu(-(Q(1,2)-d)*L)
       +k*(Q('2.67')*eu(-(Q(2,3)-d)*L)+(1+Q(4,H)/L)*J(L,d)+2*eu(-(1-d)*L))
       +Q('.502')*eu(-(1-d)*L))
    e=B*eu(-d*L)/L
    assert e<1
    return B/(1-e)
def logscale(L,d,mode):
    e=E(L,d,mode)
    assert e/L<1
    return L*L*e/(1-e/L)
def logray(A,K,B,d=D,verify=True):
    A,B,K=Q(A),Q(B),Q(K)
    assert Q("43.7")<=A<=B
    # L^2 E(plateau) is convex up to B, and E(plateau)/L decreases.
    # Bound numerator and denominator separately on the interval.
    size=max(A*A*E(A,d,'plateau'),B*B*E(B,d,'plateau'))
    v=max(size/(1-E(A,d,'plateau')/A),logscale(B,d,'power'))
    print('log ray',d,A,K,B,float(v),'slack',float(K-v),flush=True)
    if verify:assert v<=K
    return v
def power(A,T,d=D,verify=True):
    A,T=Q(A),Q(T)
    r=U(A,d)
    print('power ray',d,A,T,float(r),'slack',float(T-r),flush=True)
    if verify:assert r<=T
def under(Q0,d=D):
    # Lower normalized log primorial margin in units exp(-L/2)/L
    A,B=Q('84.5'),Q(Q0)
    assert B>=A
    k=1+1/A
    qw=(A+2)/(A*(A+1))
    return (Q('.9999')*(2-4*qw)
            -k*(Q('.048')+(1+Q(4,H)/A)*J(B,d)*eu((Q(1,2)-d)*B)+2*eu(-A/2))
            -Q('.502')*eu(-A/2))

def prim(A,d=D):
    # Multiplying each log bound by L exp(delta L) makes remainders monotone.
    L=Q(A)
    k=1+1/L
    r=eu(-d*L)
    p=(F(L,d)+Q('1.000000147')*eu(-(Q(1,2)-d)*L)+Q('1.78')*eu(-(Q(2,3)-d)*L))
    assert p*r<Q('1e-12')
    s=eu(-(Q(1,2)-d)*L)
    t=eu(-(Q(2,3)-d)*L)
    x=eu(-(1-d)*L)
    i=k*(Q('.048')*s+(1+Q(4,H)/L)*J(L,d)+2*x)
    v=Q('.50001')*k*p*p*r
    b=v+k*(Q('2.0000003')*s+Q('2.67')*t)+i
    a=i+Q('.502')*x
    assert b*r/L<1
    return a,b/(1-b*r/L)
if __name__=='__main__':
    import sys
    if sys.argv[1:]==['scout']:
        for a in ('65','66','67','68','69','70','71','72','73','74','80','100','120','150'):
            logray(a,'2.99e-8',169,verify=False)
        for a in (165,168,169,170,190,200,250,400,600,1000,2500,10000,100000,1000000,5000000):
            power(a,1,verify=False)
        for b in (90,92,94,96,98,100,101,102,103,104):
            print('positivity bound',b,float(under(b)),float(under(b,D0)),flush=True)
        for a in (170,180,185,190,200,210,220,230,240,250,300,400,1000):
            print('primorial',a,tuple(map(float,prim(a))),flush=True)
