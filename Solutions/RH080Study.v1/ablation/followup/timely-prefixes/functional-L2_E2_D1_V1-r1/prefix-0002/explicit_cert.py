'''Rational checks for the general-witness explicit argument in explicit.md.'''
from pathlib import Path
from fractions import Fraction as Q
from runpy import run_path
import json,sys
SRC=Path('/corpus/literature/Blanquer_supplement/certificates')

def log_series(x):
    z=(x-1)/(x+1)
    assert 0<=z<=Q(1,3)
    N=32
    a=2*sum((z**(2*k+1)/(2*k+1) for k in range(N)),Q())
    return a,a+2*z**(2*N+1)/((2*N+1)*(1-z*z))
LOG2=log_series(Q(2))
def logs(x):
    assert x>0
    if x<1:
        a,b=logs(1/x);return -b,-a
    k=0
    while x>=2: k+=1;x/=2
    a,b=log_series(x)
    return a+k*LOG2[0],b+k*LOG2[1]

def exup(x):
    assert 0<=x<1
    return 1/(1-x)

def area(a,b):
    a,b=sorted([a,b])
    if b<=0:return Q()
    if a>=0:return (a+b)/2
    return b*b/(2*(b-a))

def main():
    p=SRC/'witness-ap.json'
    w=json.loads(p.read_text())
    m=w['m']; a=[Q(v,w['scale']) for v in w['coefficients']]+[Q()]
    assert len(a)==5*m+1 and a[-1]==0 and w['A']=='4'
    A0=(2*sum(map(abs,a))-abs(a[0]))/m
    F0=(2*sum(a)-a[0])/m
    J=2*sum(area(x,y) for x,y in zip(a[m:],a[m+1:]))/m
    D4=F0-4*J
    assert 0<D4<1
    V0=2*sum(abs(y-x) for x,y in zip(a,a[1:]))
    sl=[m*(y-x) for x,y in zip(a,a[1:])]+[Q()]
    V1=2*abs(sl[0])+2*sum(abs(y-x) for x,y in zip(sl,sl[1:]))
    wplus=[max(0,x) for x in a[m:]]
    HW=wplus[0]+sum(max(0,y-x) for x,y in zip(wplus,wplus[1:]))
    B=20*(2*sum(abs(v)*(j*j+Q(1,6)) for j,v in enumerate(a))-abs(a[0])/6)/m**3
    assert A0<Q('1.004') and max(map(abs,a))<Q('.692')
    assert V0<Q('1.405') and V1<Q('4.062') and HW<Q('.11428')
    assert F0>Q('.999999999') and B<Q('4.955') and J<Q('.020372')

    # Uses the assigned supplement exact-integer norm verifier, not Arb output.
    # Default runs it; --cached uses Table 1's printed integer upper endpoint instead.
    if '--cached' in sys.argv:
        ratio_cap=Q('0.851127042054')
    else:
        v=run_path(str(SRC/'certify_integer.py'))['verify'](p,2**20)
        print('assigned integer FFT:',v['ratio_upper_bound'])
        ratio_cap=Q(v['ratio_upper_bound'])
    U=Q('.781772'); D=Q('.91851379')
    assert ratio_cap*D4<U

    X=Q(4*10**18); sqX=Q(2*10**9); t0=Q(42); tup=Q(43)
    d0=Q(1,10**8); lam=5*d0; dt=Q(2,10**9); cmax=Q('.86')
    assert t0<logs(X)[0] and logs(X)[1]<tup
    assert cmax*tup/(2*sqX)<d0
    pil=Q('3.14'); assert d0/(2*pil)<dt
    assert Q(1,2)*(1-d0)>Q('.49999999')
    assert cmax*cmax*tup*tup/(4*sqX)<Q('.001')
    assert exup(d0/2)*cmax/2<Q('.431')

    # Pole and base exterior multiplier at t>=42.
    assert 4*(1+lam/t0)*exup(3*lam/2)<Q('4.000001')
    # cosh(z)-1 <= z^2/(1-z) via power series, 0<=z<1.
    assert F0-A0*(lam/2)**2*exup(lam/2)-Q('4.000001')*J>D

    q=12; L=Q('4.97'); assert 2*logs(Q(q))[1]<L
    Aq=Q('4.000001')/(1-L/t0)
    Ewing=2*Aq*HW/q + Aq*L*Q('.431')*J
    assert Ewing<Q('.285')

    g0=V1/(4*pil**2); g1=(5*V1+2*V0)/(2*pil)
    assert logs(1/dt)[1]<21
    err=d0*(Q('.30')*g1+(3+Q('.15')*21)*2*(Q(220,7)*A0+g1))
    assert 2*g0+err+2*A0*d0<Q('.207')
    r=Q('.45'); ell=logs(1/r)
    signed_saving=2*(F0*r*(1+ell[0])-B*r**3/3*(Q(1,3)+ell[1]))
    assert signed_saving>Q('1.277')

    Kpot=max(map(abs,a))/(2*LOG2[0])*(1+6*d0/t0)**2*exup(2*d0)*(
          tup**2+Q(5,2)*cmax*tup**3*exup(3*d0))/sqX
    assert Kpot<Q('.00005')
    Y=Q(10**18)
    assert X*(1-4*d0)>Y and d0*A0/(10**9*(Y*Y-1))<Q('1e-8')
    assert Q('1.277')-Q('.207')-Q('.285')-Q('.00005')-Q('1e-8')-Q('.001')>Q('.7839')
    # Lower bound for margin is linear plus positive log; concave in t.
    def margin(c,t):
        return (c*D-U)*t/2+U*logs(Q('.49999999')*c*t)[0]+Q('.7839')
    for c,b in [('0.8',174),('0.74',63),('0.75',70)]:
        c=Q(c)
        v=min(margin(c,t0),margin(c,Q(b)))
        print('finite:',c,b,float(v))
        assert v>0
    c=Q('.85113')
    assert c*D>U and margin(c,t0)>0
    # Finite handoff for 4<=x<X: check the only small-prime gaps directly.
    def f_lower(x): # sqrt(4)>=2, sqrt(5)>=2, sqrt(7)>=2.64
        return Q('.8')*(Q('2.64') if x==7 else 2)*logs(Q(x))[0]
    for x,y in [(4,5),(5,7),(7,11)]:assert f_lower(x)>y-x
    # 2/e < .74: e > sum_{n=0}^5 1/n! = 163/60.
    assert Q(120,163)<Q('.74')
    print('all explicit checks passed')
if __name__=='__main__':main()
