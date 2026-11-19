"""Secant layer retaining the logarithm in the original count theorem."""
from profiles import *
from decimal import ROUND_CEILING

@lru_cache(None)
def density(j,h=None):
    s=I(j)/800
    p=I(8)/3*(1-s); q=5-2*s
    _,g,c,_,_=dat(j)
    d=1-p
    # Integral of y^n exp(-D y) on [0,infty) or with damped weight.
    A=None if h is None else 2/(H*I(h))
    def gam(D,n):
        if A is None: return I(factorial(n))/D**(n+1)
        if A.r<=1: return 2*A*I(factorial(n))/(D+1)**(n+1)
        assert A.l>=1
        z=A.ln()
        # Split at z. Substitute y=z+w to compute the two upper tails.
        def tail(B):
            return ef(B,z)*sum((I(comb(n,i)*factorial(i))*z**(n-i)/B**(i+1)
                    for i in range(n+1)),I())
        return I(factorial(n))/D**(n+1)-tail(D)+2*A*tail(D+1)
    total=I()
    binom=I(1)
    for n in range(5):
        if n: binom*= (q-(n-1))/n
        total+=g*binom*gam(d,n)/ell**n
    total+=c*(gam(I(1),0)+2*gam(I(1),1)/ell+gam(I(1),2)/ell**2)
    if h is None:
        total=mini(total,dat(j)[0])
    # Certified lower moments of Z(y)^2/(1+G/2); Taylor order six.
    correction=I()
    binom=I(1)
    for n in range(7):
        if n: binom *= (2*q-(n-1))/n
        correction += binom*gam(2*d,n)/ell**n
    return total - (g*g/(4+2*g))*correction

def weight(A):
    L=ell-(2*PI).ln()
    R=I('.137')*ell+I('.443')*ell.ln()+I('1.588')
    r=I('.137')+I('.443')/ell
    q=mini(1,A)
    if A.r<=1:
        main=A*(L+1)/(2*PI)
    else:
        assert A.l>=1
        z=A.ln()
        main=(L*(z+1)+z*z/2+z+1)/(2*PI)
    return main+q*(2*R+r)/H

@lru_cache(None)
def coeff(cap,h=None):
    if h is not None:
        A=2/(H*I(h))
        W=weight(A)
    vals=[I(density(j,h).r) for j in range(s0i,cap+1)]
    # The true integrated majorant decreases in s, even though independent
    # upper enclosures at the nodes need not.
    for i in range(1,len(vals)): vals[i]=mini(vals[i],vals[i-1])
    if h is not None:
        W=I(W.r)
        i=next((i for i,v in enumerate(vals) if v.r<=W.r),len(vals))
        if i: vals[:i+1]=[W]*min(i+1,len(vals))
    ds=[b-c for b,c in zip(vals[:-1],vals[1:])]
    assert all(v.l>=0 for v in ds)
    if h is not None: assert (W-vals[0]).l>=0 or W.l==vals[0].l
    return vals[0],vals[-1],ds,W if h is not None else None

def sec_norm(u,cap,h=None):
    # Output is normalized by exp(-a u).
    u=I(u)
    a=1-I(cap)/800
    first,last,ds,A=coeff(cap,h)
    if A is None:
        A=U(u)
        assert u.l>=140 and (A-2*first).l>0
    f=ef(I(1)/800,u)
    poly=I()
    for v in ds: poly=poly*f+v
    layer=last+maxi(0,A-first)*f**len(ds)+(1-f)*poly/(u/800)
    h=ef(I('.25'),u) if h is None else I(h)
    return (1+2*h)*(h/2/ef(a,u)+116*ef(I('.5')-a,u)+
                     A*ef(s0-a,u)+layer)+2*ef(1-a,u)

def sec(u,cap,h=None):
    return sec_norm(u,cap,h)*ef(1-I(cap)/800,u)

def analytic_power(u,cap):
    a=1-I(cap)/800
    return sec_norm(u,cap)+allowance(u,a)

def allowance(u,a):
    return I('1.212')*ef(I('.5')-a,u)+21/I(H)+3*ef(1-a,u)

def product_cost(z,u,a):
    return z*(z*ef(a,u)/u).exp()


WINS=('1.05e-12','1e-12','2e-13','1.5e-13','1e-13','7e-14','5e-14',
      '3.5e-14','2e-14','1e-14','7e-15','5e-15','3e-15','2e-15','1e-15')
