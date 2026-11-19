"""Secant-layer improvement and its numerical certificates."""
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
    return mini(total,dat(j)[0]) if h is None else total

@lru_cache(None)
def coeff(cap,h=None):
    if h is not None:
        A=2/(H*I(h))
        if A.r<=1: W=A*(ell+1)/3
        else:
            assert A.l>=1
            z=A.ln()
            W=(ell*z+z*z/2+2*(ell+z+1))/6
    vals=[I(density(j,h).r) for j in range(s0i,cap+1)]
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
POWER=[
    (170,'.01444',None),(184,'.0134','.234'),(190,'.01285','.2265'),
    (200,'.01228','.21614'),(250,'.01051','.18432'),(300,'.00959','.16793'),
    (400,'.00865','.15116'),(600,'.00787','.13746'),(1000,'.00734','.12817'),
    (2000,'.006990','.12198'),(10000,'.006729','.11739')
]
EARLY='166.4'
EARLY_C='.235'

def checkM():
    a=I(5)/32
    ib=I(1)/8
    assert coeff(basecap)[1].l>D('.0066') and coeff(basecap)[1].r<D('.006665')
    assert coeff(newcap)[1].r<D('.11625')
    print('cap limiting coefficients',coeff(basecap)[1].r,coeff(newcap)[1].r)
    for L,c0,c1 in POWER:
        for cap,c in ((basecap,c0),(newcap,c1)):
            if c:
                u=I(L); a2=1-I(cap)/800
                r=product_cost(analytic_power(u,cap),u,a2)
                assert r.r<D(c),(L,c,r)
        print('refined power closed ray',L,c0,c1)
    # For a fixed averaging width the mode-normalized bound is convex,
    # including the allowance. Use a uniform conversion at the left end.
    # Keep the two named choices for the first two slabs for a strict comparison.
    segments=[(D(EARLY),D('167')), (D('167'),D('168'))] + [
        (D(k)/4,D(k+1)/4) for k in range(672,736)]
    for k,(l,r) in enumerate(segments):
        U=I(l); V=I(r)
        hs=((WINS[k],) if k<2 else WINS)
        cand=[]
        for h in hs:
            for mode in range(2):
                if k<2 and mode==0: continue
                vals=[(sec_norm(t,newcap,h) if mode else spectral(t,newcap,h)/ef(a,t))
                         +allowance(t,a) for t in (U,V)]
                cand.append((product_cost(I(max(v.r for v in vals)),U,a).r,h,mode))
        c,h,mode=min(cand)
        assert c<D(EARLY_C),(l,r,c,h)
        print('bridging slab',l,r,'width',h,'secant' if mode else 'step',
              HI.quantize(c,D('.000000001')))
    for l,h in ((EARLY,WINS[0]),('167',WINS[1])):
        u=I(l)
        absolute=(sec_norm(u,newcap,h)+allowance(u,a))*ef(a,u)
        assert (absolute*(absolute/u).exp()).r<D('1.042e-12')
    assert (PI/H).l>D('1.047e-12')
    assert (I('.235')*ef(a,I(168))).r<D('9.5e-13')
    assert (I('.235')*ef(I(1)/32,I(168))).r<D('.0016')
    # Match the refined simple rays on u>=200.
    assert (I('.21614')/I('.01228')*ef(I(1)/32,I(200))).r<D('.0341')

def finite_tail():
    from mertens import prime_powers
    low=I(10**7).ln(); high=I(10**13).ln()
    s=I('.1')+I(20)/H*ef(-I(3)/8,high)+2*ef(I('.5'),low)
    x=I(60000000).ln()
    weighted=(I('.791')+s+prime_powers(x)[1]/ef(I('.5'),x))*x*x*ef(I('.5'),x)
    z=(I('.791')+s+s/x)*x*x*ef(I('.5'),x)+prime_powers(x)[3]*x**3
    print('60 million analytic join: products and sum 1/p, weighted',
          (z*(z/x**3).exp()).r, weighted.r)
    assert max((z*(z/x**3).exp()).r,weighted.r)<D('.082')

if __name__=='__main__':
    checkM()
    finite_tail()
