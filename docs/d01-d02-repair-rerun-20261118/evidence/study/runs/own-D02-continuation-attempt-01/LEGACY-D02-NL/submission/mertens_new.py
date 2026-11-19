"""Outward rational checks for signed spectral envelopes and new onsets.

Use '/usr/bin/python3.10 mertens_new.py /work/repaired.out' (ordinary
assertions). The argument file must be the freshly generated stdout from
sieve_repaired.c. Analytic checks may be run without the file.
"""
from D01_check import I, F, exp, log, rng, less, approx, check_mertens, LN2
from power import Q, J, H, A, mass, c
from pathlib import Path

a=I('1.048e-12')
def Cbound(t,b):
    return c(t,b)
def simple_bound(t,b):
    # The 140 log derivative estimate is proved in the text.
    return mass(b)*t/(t-140)+(t*t/(9*I('6.28'))+I('1.8642'))*exp(-(b-F(3,4))*t)+I('2.091')*t*exp(-(b-F(2,3))*t)
def Jscaled(t,b):
    # e^((1-b)t) multiplied into the tail bound, using cancellation.
    return I('.0462')*exp(-(b-F(1,2))*t)+I('3.1e-12')+I('1.84')*exp(-b*t)
def add(t,b):
    # Simultaneously covers the harmonic log and weighted signed errors.
    return (1+1/t)*Jscaled(t,b)+I('1.092')*exp(-(b-F(1,2))*t)
def rel(x,t,b):
    return x/(1-x*exp(-(1-b)*t)/t)

def check_powers():
    q=F(13,4)
    less(I(F(8,3))*(A+log(3))+2*log(A)+2*sum(I(1)/(q-i) for i in range(4))+40,140)
    less(mass(Q),'.006664')
    less(mass(J),'.11625')
    for b,edge,x0,cap in [(Q,186,550000,'.01325'),(J,'167.8',10000,'.262')]:
        t=I(edge); t0=log(x0); s=log(10**8); u=log(10**13)
        # Finite certified portion: auxiliary log and weighted bound.
        M1=I('1.88')*exp(-(b-F(1,2))*t0)
        # From 1e8 to 1e13: D01 signed 1.94 bound.
        M2=I('1.94')*exp(-(b-F(1,2))*s)
        # Above 1e13 to exp(edge): convex sum, with the decreasing
        # reciprocal prefactor in the small J term frozen at u.
        def mid(v):
            return a*exp((1-b)*v)+I('114.762')*exp(-(b-F(1,2))*v)+(1+1/u)*Jscaled(v,b)
        M3=mid(u)
        M4=mid(t)
        M5=Cbound(t,b)+add(t,b)
        for M,tmin in [(M1,t0),(M2,s),(M3,u),(M4,u),(M5,t)]:
            less(rel(M,tmin,b),cap)
        print('closed pure power ray',b,x0,cap,flush=True)
    # Products and unweighted sum have the smaller finite logarithmic cap.
    t0=log(420000)
    less(rel(I('1.70')*exp(-F(3,8)*t0),t0,Q),'.01325')
    print('earlier unweighted and product power ray passed from 420000')
    # Fixed power improvements. Positive normalized components decrease.
    for b,n,cap,fn in [(Q,200,'.01241',Cbound),(Q,250,'.01062',Cbound),
           (Q,300,'.00969',Cbound),(Q,1000,'.00742',Cbound),
           (Q,2300,'.00703',Cbound),(Q,50000,'.00669',simple_bound),
           (Q,100000,'.00668',simple_bound),(J,200,'.21825',Cbound),
           (J,300,'.170',Cbound),(J,1000,'.130',Cbound),
           (J,50000,'.117',simple_bound)]:
        t=I(n)
        less(rel(fn(t,b)+add(t,b),t,b),cap)
        print('pure power improved coefficient',b,n,cap,flush=True)

def check_logarithmic():
    # New common strict 1/log^3,1/log^2 cap rows.
    # t up to log(1e13), via the signed spectral bound.
    b=Q; u=log(10**13); v=I(57); w=I(186)
    for xx,k in [(2*10**8,'.051'),(10**9,'.027'),(10**10,'.0105')]:
        t=log(xx); k=I(k)
        p=I('1.94')*t*t*exp(-t/2)
        less(p/(1-p/t**3),k)
    # finite RH from 10^13 to e^57, then CH2 to e^186.
    # x >= exp(186): density powered, decays after normalization.
    def mid(v,w):
        return I('.04')*v**4*exp(-v/2)+(I('1.092')+I('.0462')*(1+1/v))*v*v*exp(-v/2)+(1+1/v)*(I('3.1e-12')*v*v*exp(-v/8)+I('1.84')*v*v*exp(-v))
    def later(v,w):
        return a*w*w+I('114.762')*v*v*exp(-v/2)+(1+1/v)*(I('.0462')*v*v*exp(-v/2)+I('3.1e-12')*v*v*exp(-v/8)+I('1.84')*v*v*exp(-v))
    end=(Cbound(w,b)+add(w,b))*w*w*exp(-w/8)
    for t,k in [(u,'.0105'),(I(34),'.00227'),(I(36),'.00105'),(I(38),'.00048'),(I(40),'.00022'),(I(42),'.000096'),(I(45),'.0000282'),(I(50),'.00000352'),(I(55),'.000000422'),(I(57),'.000000193'),(I(60),'.000000075'),(I(65),'.0000000400'),(I(70),'.0000000370')]:
        k=I(k)
        for p in ([mid(t,v)] if t.a<v.a else [])+[later(I(max(t.a,v.a),max(t.b,v.b)),w),end]:
            less(p/(1-p/t**3),k)
        print('scaled log-ray verified',approx(t)[0],approx(k)[0])
    less(v,log(I('2.169e25')))
    less(I('.04'),1) # rate proof and exact pi checks use the other source constants.

def compare():
    d=I('.01325')
    def f(t):
        t=I(t);return d*t*t*exp(-t/8)
    for lo,hi,y in [(35,36,'.2'),(28,29,'.3')]:
        less(y,f(lo))
        less(f(hi),y)
    less('.3',d*log(420000)**2*exp(-log(420000)/8))
    less(c(I(185),Q),I('.0106')*251/(251-92))
    less(c(I(251),Q),'.0106')
    less(c(I(200),Q)*50300,625)
    print('strict whole-domain and crossover comparisons verified')

def check_anchor(path):
    rows=Path(path).read_text().splitlines()
    assert 'clipped auxiliary segment 9973 10007 at 10000' in rows
    assert 'finite Mertens certificate passed; N=100000000, prime count=5761455' in rows
    w=next(r.split()[3:] for r in rows if r.startswith('anchor 2278379 2278421 '))
    zl,zh=map(int,w[:2])
    A=exp(rng(F(zl,2**60),F(zh,2**60)))
    def p(x):
        t=log(I(x))
        return (1-t/A)*t**3
    less(A,4*log(2278379)/3) # scaled P error decreasing
    less(log(2278421),A)  # positive signed log Q across the gap
    for u,v,m in [('2278381.575','.2','lower'),('2278381.577','.2','upper'),
                  ('2278381.59','.199999','upper'),('2278381.69','.19999','upper'),
                  ('2278381.81','.19998','upper')]:
        less(I(v),p(u)) if m=='lower' else less(p(u),I(v))
    print('P-only exact sharp root and stricter earlier rows passed')

if __name__=='__main__':
    import sys
    check_mertens()
    check_powers()
    check_logarithmic()
    compare()
    if len(sys.argv)>1: check_anchor(sys.argv[1])
