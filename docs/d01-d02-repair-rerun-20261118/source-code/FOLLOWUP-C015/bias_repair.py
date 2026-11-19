"""Exact finite higher-power bias with an analytic prime tail; no normalized (9.1)."""
from mertens import *
from bisect import bisect_right
from functools import lru_cache

@lru_cache(None)
def make_bias():
    N=10**5
    X=4_000_000_000
    K=I('.007')
    a=I(N).log(); z=I('29.9')
    assert low(N*N,X) and low(X,ex(I(22))) and N>=10**4
    # Whole theta ray beyond N: CH2 unweighted, finite RH, CH2 Cor. 1.3.
    assert low(K, I('1.791000147')*ex(-a/2)+I('1.78')*ex(-2*a/3))
    assert low(K,mx(z*z/(8*PI)*ex(-z/2),thetaCH(I(58))))
    main=-I.raw(*lnq(N-1,N))
    width=K*(2*I(1)/(N-1)+main)
    const=main+bracket(-width,width)
    mainA=(1-1/a+2/a**2-6/a**3+24/a**4)/(2*N*a)
    alower=mainA-120/(2*N*a**6)
    wa=K*3/(2*N*a)
    rem=I(1)/(3*(N-1)**2)
    cA=I.raw((alower-wa).lo,(mainA+wa+rem).hi)
    # Finite prime contribution to A, using an explicit positive remainder.
    cut=10**24
    cA+=bracket(0,F(2*N,cut))
    steps=[]
    for p in sieve(N):
        lp=I(p).log()
        const+=lp/(p*(p-1))
        q=p*p
        j=2
        while q<=cut:
            aa=I(1)/(j*q)
            cA+=aa
            if q<=X:steps.append((q,lp/q,aa))
            q*=p
            j+=1
    steps.sort(key=lambda t:t[0])
    powers=[]; values=[const]; avals=[cA]
    for q,m,aa in steps:
        powers.append(q)
        const-=m
        cA-=aa
        values.append(const)
        avals.append(cA)
    print('bias table powers',len(powers),'primes to',N,'x cap',X,'tail',main+bracket(-width,width))
    def bias(L):
        x=ex(L)
        a=bisect_right(powers,x.lo//S)
        b=bisect_right(powers,x.hi//S)
        return I.raw(values[b].lo,values[a].hi),I.raw(avals[b].lo,avals[a].hi)
    return bias

if __name__=='__main__':
    f=make_bias()
    for l in ['13','15.8','15.9','16','16.1','17','17.6','18','22']:
        L=I(l)
        print('single point diagnostic',l,[z*L**(3 if j<3 else 2) for j,z in enumerate(bounds(L,finite_bias=f))])
    for start,c,d in [
        (16,'.185','.175'),(16,'.160','.167'),(F('15.89'),'.185','.175'),
        (F('15.7'),'.185','.19'),(F('15.5'),'.185','.2'),
        (F('17.6'),'.09','.09'),(F('17.7'),'.09','.09')
    ]:
        for row in [[(3,c)]*3+[(0,0)],[(0,0)]*3+[(2,d)]]:
            try:
                test_poly(start,240,row,finite_bias=f)
            except ValueError as e:
                if start!=F('15.5') and (start,row[-1])!=(F('17.6'),(2,'.09')): raise
                print('sufficient-test failure',start,row,e)
    from density_repair import sc, boot_height
    boot_height()
    def tighter(L):return sc(L)*ex(-L/8)
    for c in ['.0197','.0198','.0199','.020']:
        try: test_early_power(c,finite_bias=f,spectral=tighter)
        except AssertionError as e:
            if c not in ('.0197','.0198'):raise
            print('sufficient-test failure early power',c,e)
