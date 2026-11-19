"""Pointwise finite bound, conservatively combined with analytic branches."""
from repair_evaluate import *
from second_finite import normalizers, LIMIT, sieve

def finite(x):
    assert 1<x<=LIMIT
    g,M,B=normalizers()
    prod,a,b=I(1),I(),I()
    n=int(x)
    if n>=2:
        for p,bit in enumerate(sieve(n)):
            if bit:
                prod*=I(p)/(p-1)
                a+=I(1)/p
                b+=I(p).ln()/p
    u=I(x).ln()
    q=prod/(g.exp()*u)
    return [maxi(v,-v) for v in (1/q-1,q-1,a-u.ln()-M,b-u+B)]

if __name__=='__main__':
    x=D(argv[1])
    assert x.is_finite()
    vals=finite(x)
    for cap in (basecap,newcap):
        us=m_augment(I(x).ln(),cap,x)
        print(cap,[min(a.r,b.r) for a,b in zip(vals,us)])
