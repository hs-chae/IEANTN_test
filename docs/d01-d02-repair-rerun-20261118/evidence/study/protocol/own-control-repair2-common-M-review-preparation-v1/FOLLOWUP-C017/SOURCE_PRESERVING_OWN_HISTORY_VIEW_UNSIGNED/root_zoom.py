"""Narrow the terminal bracket with the inherited integer join unchanged."""
from endpoint import *
from decimal import localcontext

n=38358837682
p=primepi(n)
q=primepi(int((n/E).l))
assert p==1644673232 and q==632207037
assert primepi(n+1)==p and primepi(int(((n+1)/E).r))==q

def R(v):
    a=I(v)
    return E*a/a.ln()*q-p*p

with localcontext() as ctx:
    ctx.prec=160  # dyadic midpoint exact through 110 iterations
    a,b=D(n),D(n+1)
    for k in range(110):
        m=(a+b)/2
        z=R(m)
        assert z.r<0 or z.l>0
        if z.r<0:a=m
        else:b=m
    # Print short, outward decimal endpoints rather than full dyadic expansions.
    l=a.quantize(D('1e-32'),rounding=ROUND_FLOOR)
    r=b.quantize(D('1e-32'),rounding=ROUND_CEILING)
    assert R(l).r<0<R(r).l
    print('strict root bracket',l,r)
    print('R signs',R(l),R(r))
