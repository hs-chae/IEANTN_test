"""New signed Mertens envelope and earlier arbitrary-order Ramanujan profiles."""
import sys
from spectral02 import *
import mertens02 as m
import ramanujan as r
import ramanujan_orders as ro
from bias_repair import make_bias

def modes_for_pi(h,a,o,z):
    return RM[h,a,o,z]

def j_integrated(L,z=0):
    return I('.12')*ex(-L/2)+I('8e-12')*ex(-(GAP0 if z else GAP)*L)

def mertens_bounds(L,z=0,**kw):
    return m.bounds(L,spectral=lambda u:spectral(u,(BETA,BETA0)[z]),gap=(GAP0 if z else GAP),**kw)

def scaled_M(L, ms, z):
    g=GAP0 if z else GAP
    assert L.lo>=180*S or low(ex(L/2),767135587)
    assert low(I('.001'), I('.5')/(L/2)**3)
    j=I('.12')*ex(-(F(1,2)-g)*L)+I('8e-12')
    u=eval4(L,ms,g)+(1+1/L)*j+I('1.84')*ex(-(1-g)*L)
    u+=I('1.002')*ex(-(F(1,2)-g)*L)+I('2.67')*ex(-(F(2,3)-g)*L)
    q=u*ex(-g*L)/L
    assert low(1,q)
    return u/(1-q)

def m_tail(B,C,z=0):
    B=F(B)
    L=I(B)
    assert low(ex(L/2),767135587)
    best,name=min((scaled_M(L,ms,z).hi,str(name)) for ms,name in scaled_ms(B,z))
    assert low(C,I.raw(best,best)),(B,C,best/S)
    print('Mertens tail',B,C,z,'scaled cap',best/S,name,flush=True)

def finite_m(C,A,B,z=0):
    A,B,C=map(F,(A,B,C))
    g=(GAP,GAP0)[z]
    bias=make_bias()
    def test(a,b):
        L=bracket(a,b)
        if a>=112:
            # A cheap guard that handles the long bridge region.
            # Compare the scaled whole-cell radii, keeping the low-x guards.
            ee=m.mn(m.thetaCH(L),spectral(L,(BETA,BETA0)[z]))
            u=(ee+(1+1/L)*j_integrated(L,z)+I('1.84')*ex(-L)+I('1.002')*ex(-L/2)+I('2.67')*ex(-2*L/3))
            if low(I(C)*ex(-g*L),u/(1-u/L)):return
        W=mertens_bounds(L,z,finite_bias=bias)
        if all(low(I(C)*ex(-g*L),v*(L if i<3 else 1)) for i,v in enumerate(W)):return
        if b-a<F(1,8192):raise ValueError((a,b,C,W))
        x=(a+b)/2
        test(a,x);test(x,b)
    assert low(ex(I(56)),767135587) and low(I('.001'),I('.5')/56**3)
    cuts=sorted({A,B,*[F(t) for t in range(int(A)+1,int(B)+1) if A<t<B],
                 *[t for t in [F('29.9')] if A<t<B]})
    for a,b in zip(cuts,cuts[1:]):test(a,b)
    print('Mertens finite cover',A,B,C,z,flush=True)

# Use oscillatory integration of psi for pi, without a growing relative
# anchor cost. Same absolute bound as the old finite branch.
def integ(L,z=0):
    beta=(BETA,BETA0)[z]
    L=I(L)
    a=I(8)
    r8=ex(4)*(8**2+8)/(8*PI)
    q=beta/(beta-F(1,4))
    r1=I('.12')*(2*ex(-L/2)/L+L*ex(4-L)/64)
    r2=I('8e-12')*(q*ex(-(1-beta)*L)/L+L*ex(8*beta-L)/64)
    small=(I('1.84')/8+r8)*L*ex(-L)
    powers=(4*I('1.000000147')*ex(-L/2)+I('21.36')*ex(-2*L/3))/L
    return r1+r2+small+powers

def integ_split(L,z=0):
    beta=(BETA,BETA0)[z]
    T=L-8
    # Bounds for Le^{-L} times the integral of exp(Bv)/v^2 on each segment.
    def pair(B):
        return (L*ex(B*T-L)/(T*T*(B-F(1,4))),
                ex(-(1-B)*L)/(L*(B-2/T)))
    r8=ex(4)*(8**2+8)/(8*PI)
    small=(I('1.84')/8+r8)*L*ex(-L)
    low0,low1=pair(F(1,2)); high0,high1=pair(beta)
    t0,t1=pair(F(1,3))
    f=I('.12')*(ex(-L/2)/L+L*ex(4-L)/64+low0/4+low1*2/T)
    h=I('8e-12')*(ex(-(1-beta)*L)/L+L*ex(8*beta-L)/64+high0/4+high1*2/T)
    return f+h+small+I('1.000000147')*(low0+low1)+I('1.78')*(t0+t1)

def pi_bound(L,z=0):
    # Same formulas and the same non-D02 floor, to permit same-method ablation.
    p=m.thetaCH(L)
    if L.hi<=58*S:
        b=L*L*ex(-L/2)/(8*PI)
        if L.lo>=34*S:
            for h in [F(1,2),F(13,20),F('.55'),F('.60')]+([F(2,5)] if L.lo>=35*S else []):
                b=m.mn(b,optimized_ch(L,ratio=h)+r.sm[2][0]*ex(-L/2)+I('1.78')*ex(-2*L/3))
        p=m.mn(p,b)
    if L.lo>=86*S:
        p=m.mn(p,spectral(L,(BETA,BETA0)[z])+I('1.000000147')*ex(-L/2)+I('1.78')*ex(-2*L/3))
    q=p+integ(L,z)
    if L.hi<=58*S:q=m.mn(q,p+integ_split(L,z))
    return m.mn(ro.new_error(L),q) if L.hi<=10000*S else q

# Positive upper at B for the monotone scaled independent-variable tail.
# Cutoff bounds are modes of c*(L-origin)^k, all increase their polynomial
# factor no faster than k/(L-origin).
def pi_modes(B,d,z=0):
    beta=(BETA,BETA0)[z]; g=1-beta
    q=beta/(beta-F(1,4))
    c=I('1.000000147')
    # For arguments >= B-1, bound inverse L factors by 1/(B-1).
    X=B-1
    L=I(X)
    rest=[
        (c+(I('.24')+4*c)/L,F(1,2),0,0),
        (I('1.78')+I('21.36')/L,F(2,3),0,0),
        (I('8e-12')*q/L,g,0,0),
        (I('.12')*ex(4)/64+I('8e-12')*ex(8*beta)/64+
           I('1.84')/8+ex(4)*(8**2+8)/(8*PI),F(1),1,0)]
    ms=[[(c,g,k,0) for c,g,k in (n if z else m)] for h,a,m,n in HMOD if X>=a]
    ms.extend(m for (h,a,o,j),m in RM.items() if z==j and X>=a)
    def check(c,g,k,a):
        return (X>a and g>=F(d+5,X)+F(k,X-a)) if k else g>=F(d+5,X)
    allm=[m+rest for m in ms if all(check(*v) for v in m+rest)]
    if not allm: return None
    return allm

def pi_mode_select(B,d,z):
    opts=pi_modes(B,d,z)
    return min(opts,key=lambda m:eval4(I(B-1),m,(GAP,GAP0)[z]).hi) if opts else None

def li_residual(B,C,z=0):
    B=F(B); X=B-1
    g=(GAP,GAP0)[z]
    best=None
    for rows,name in scaled_ms(X,z):
        # Restore the exact same integrated/prime-power correction as pi_modes.
        beta=1-g; q=beta/(beta-F(1,4)); L=I(X)
        r0=ex(-(F(1,2)-g)*L);r1=ex(-(F(2,3)-g)*L)
        c=I('1.000000147')
        extra=(c+(I('.24')+4*c)/L)*r0+(I('1.78')+I('21.36')/L)*r1+I('8e-12')*q/L
        extra+=(I('.12')*ex(4)/64+I('8e-12')*ex(8*beta)/64+
           I('1.84')/8+ex(4)*(8**2+8)/(8*PI))*L*ex(-(1-g)*L)
        u=eval4(L,rows,g)+extra
        vb=sum(c/I(B)**k for k,c in enumerate(r.U))
        v=u*(B/X*ex(I(g))+2*vb+u*ex(-g*I(B)))
        if best is None or v.hi<best[0]:best=(v.hi,str(name),u.hi)
    assert best is not None and low(C,I.raw(best[0],best[0]))
    print('li residual tail',B,C,z,'scaled cap',best[0]/S,'pi cap',best[2]/S,best[1],flush=True)

def tail_R(B,d,z=0, m=None, exact=False):
    B=F(B);X=B-1
    if B.denominator!=1:return False
    B=int(B);X=int(X)
    N,up,co=ro.coeffs(d)
    A=max(32,2*(N+1))
    if not (X>A and 2*X**(N+1)*1000**(X-A)<fac(N)*2718**(X-A)):return False
    h=ro.full(N-1)+sum(F(v,B**j) for j,v in enumerate(co,1) if v<0)
    if h<=0:return False
    m=pi_mode_select(B,d,z) if m is None else m
    if m is None:return False
    def er(X,scale=0):
        t=I(B).log()*scale
        return sum(c*(X-a)**k*ex(t-g*X) for c,g,k,a in m)
    p=sum(F(v,B**k) for k,v in enumerate(up))
    if exact:
        def q(V):
            return sum(F(cv(c).hi,S)*(V-a)**k*F(1000,2718)**int(g*V) for c,g,k,a in m)
        u,v=q(B-1),q(B)
        return h>B**(d+5)*(F(B,B-1)*u+v*(2*p+v))
    q1,q2=er(B-1,d+5),er(B,d+5)
    return low(h,F(B,B-1)*q1+q2*(2*p+er(B)))

def ats(d,z=0):
    # Opt for a single compact mode in fast endpoint searching.
    exact=False
    assert low(E,F(2718,1000))
    def ck(B):
        X=B-1
        h,a,o=F(1,4),112,F('.775')
        opts=pi_modes(B,d,z)
        if not opts:return False
        m=next((v for v in opts if v[:len(RM[h,a,o,z])]==RM[h,a,o,z]),None)
        if m is None:m=opts[0]
        return tail_R(B,d,z,m,exact=exact)
    lo=8;hi=160
    while not ck(hi):
        hi*=2
        if hi>=65536:exact=True
    while hi-lo>1:
        j=(lo+hi)//2
        if ck(j):hi=j
        else:lo=j
    assert ck(hi)
    return hi

from math import factorial as fac
