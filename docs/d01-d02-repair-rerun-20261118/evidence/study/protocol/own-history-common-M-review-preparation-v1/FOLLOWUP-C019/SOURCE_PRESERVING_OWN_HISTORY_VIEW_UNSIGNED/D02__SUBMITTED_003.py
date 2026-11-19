"""Exact local Ramanujan endpoint check, no prime data or floats."""
from math import isqrt
from fractions import Fraction as F
from ray_check import ei
from mertens_check import sieve

def unit_log(y):
    assert 1<=y<=2
    z=(y-1)/(y+1)
    a=2*sum(z**(2*j+1)/(2*j+1) for j in range(60))
    return a,a+2*z**121/(121*(1-z*z))

LL,LU=unit_log(F(2))
def lu(x):
    x=F(x)
    h=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/2**h
    if y<1:
        y*=2
        h-=1
    assert h>=0
    a,b=unit_log(y)
    return h*LL+a,h*LU+b

def primecount(n):
    if n<2:
        return 0
    r=isqrt(n)
    vs=[n//i for i in range(1,r+1)]
    vs+=list(range(vs[-1]-1,0,-1))
    s={v:v-1 for v in vs}
    for p in range(2,r+1):
        if s[p]==s[p-1]:
            continue
        sp=s[p-1]
        pp=p*p
        for v in vs:
            if v<pp: break
            s[v]-=s[v//p]-sp
    return s[n]

def main():
    # Independent small input checks against an elementary Eratosthenes sieve.
    sv=sieve(500)
    assert all(primecount(n)==sum(sv[:n+1]) for n in range(501))
    N=38358837682
    M=14111427770
    assert (N+1)%2521==0 and 1<2521<N+1
    el,eu=ei(F(1))
    assert M*eu<N<=N+1<(M+1)*el
    P,Q=primecount(N),primecount(M)
    assert (P,Q)==(1644673232,632207037)
    def gap(x):
        l,u=lu(x)
        return el*x*Q/u-P*P,eu*x*Q/l-P*P
    # Rational sign tests for the proposed bracket. The points are real,
    # and lie in the same no-jump cell of both pi factors.
    l=N+F('0.21792636514465772878')
    r=N+F('0.21792636514465772879')
    assert gap(l)[1]<0<gap(r)[0]
    assert gap(N+F(1,10))[1]<0<gap(N+1)[0]
    Ll,_=lu(N)
    _,Lu=lu(N+1)
    assert 67_000_000<el*Q*(Ll-1)/Lu**2
    assert eu*Q*(Lu-1)/Ll**2<68_000_000
    print(P,Q,str(l),str(r),flush=True)
    print("Ramanujan real endpoint certificate passed",flush=True)

if __name__=='__main__':
    main()
