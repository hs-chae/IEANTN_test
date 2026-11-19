"""New closed-ray and transition checks; all simple rows strict."""
from log_layer import *
from repair_spectral import coeff as oldcoeff
from mertens import prime_powers

WIDER=WINS+('9e-13','8e-13','6e-13','4e-13','3e-13','7e-16','3e-16','1e-16',
           '3e-17','1e-17','3e-18','1e-18','3e-19','1e-19','3e-20','1e-20')
TABLE=[
    (250,'.010496','.181831'),(300,'.009578','.166055'),
    (400,'.008636','.149754'),(600,'.007862','.136335'),
    (1000,'.007337','.127204'),(2000,'.006986','.121110'),
    (10000,'.006726','.116580'),
]
BRIDGES=[
    (basecap,185,198,'.01239'),(newcap,166,185,'.22775'),
    (newcap,190,193,'.2200'),
    (basecap,200,204,'.01218'),(newcap,200,201,'.21150'),
]
@lru_cache(None)
def ZZ(v,cap,h):
    u=I(v)
    return (sec_norm(u,cap,h)+allowance(u,1-I(cap)/800)).r

def bridge(cap,L,R,C):
    a=1-I(cap)/800
    rows=[]
    for j in range(8*L,8*R):
        l=D(j)/8
        r=D(j+1)/8
        zs,h=min((max(ZZ(l,cap,h),ZZ(r,cap,h)),h) for h in WIDER)
        z=product_cost(I(zs),I(l),a).r
        assert z<D(C),(cap,l,r,z,h,C)
        rows.append((z,l,h))
    return max(rows)

def mtail(L,cap,C):
    u=I(L)
    assert product_cost(analytic_power(u,cap),u,1-I(cap)/800).r<D(C)

def power():
    for cap,L,R,C in BRIDGES:
        z,w,h=bridge(cap,L,R,C)
        mtail(R,cap,C)
        print('bridge',cap,L,R,C,HI.quantize(z,D('.000000001')),w,h,flush=True)
    for cap,R,C in [(basecap,185,'.01239'),(newcap,166,'.22775')]:
        a=1-I(cap)/800
        U=I(17); V=I(32)
        assert (I('.117')/(V**2*ef(a,V))).r<D(C)
        def fn(u):
            return sourcefloor/ef(a,u)+115*ef(I('.5')-a,u)+21/I(H)+3*ef(1-a,u)
        z=I(max(fn(V).r,fn(I(R)).r))
        assert product_cost(z,V,a).r<D(C)
        print('left joins',cap,17,32,R,C,HI.quantize(product_cost(z,V,a).r,D('.000000001')))
    for L,b,c in TABLE:
        for cap,C in ((basecap,b),(newcap,c)): mtail(L,cap,C)
        print('default',L,b,c)
    for cap,C in [(basecap,'.0066610'),(newcap,'.1154620')]:
        assert (coeff(cap)[1]+21/I(H)).r<D(C)
        print('limiting coefficient <',cap,C)
    assert (I('.21150')/I('.01218')*ef(I(1)/32,I(200))).r<D('.03353')
    cross=32*(I('.22775')/I('.01239')).ln()
    assert D('93.16')<cross.l<cross.r<D('93.18')
    print('extended-onset simple-ray crossover',cross)

def separation():
    # Finite B0 menu: either the bias or the last term proves the old barrier.
    for h in WIDER:
        if D(h)<D('2.1e-12'):
            assert coeff(basecap,h)[1].l>D('.0016')
    assert coeff(basecap)[1].l>D('.0016')
    t=(I('.008')*ef(I('.125'),I(189))).r
    for h in WIDER:
        assert D(h)>=t or coeff(basecap,h)[1].l>D('.004')
    assert (I('.0016')*ef(I('.125'),I(168))).l>D('1.05e-12')
    assert (PI/I(3000175332800)).l>D('1.047e-12')
    for L,h in [('166.1','1.05e-12'),('167','1e-12')]:
        u=I(L)
        z=I(ZZ(D(L),newcap,h))
        assert (product_cost(z,u,I(5)/32)*ef(I(5)/32,u)).r<D('1.044e-12')
    assert (I('.22775')*ef(I(5)/32,I(168))).r<D('9.5e-13')
    assert (I('.22775')*ef(I(1)/32,I(168))).r<D('.0016')
    print('strict separated point-envelope onset',166.1)

def fin():
    low=I(10**7).ln(); high=I(10**13).ln()
    s=I('.1')+I(20)/H*ef(-I(3)/8,high)+2*ef(I('.5'),low)
    x=I(100000000).ln()
    weighted=(I('.791')+s+prime_powers(x)[1]/ef(I('.5'),x))*x*x*ef(I('.5'),x)
    z=(I('.791')+s+s/x)*x*x*ef(I('.5'),x)+prime_powers(x)[3]*x**3
    ps=(z*(z/x**3).exp()).r
    assert max(ps,weighted.r)<D('.07')
    print('100 million analytic join <',HI.quantize(ps,D('.000000001')),
          HI.quantize(weighted.r,D('.000000001')))

if __name__=='__main__':
    power()
    separation()
    fin()
