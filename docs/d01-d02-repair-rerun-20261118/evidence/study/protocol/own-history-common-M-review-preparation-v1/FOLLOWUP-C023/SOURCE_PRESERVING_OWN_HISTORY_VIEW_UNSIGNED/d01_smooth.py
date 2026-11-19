"""Exact certificates for integrated-zero formulas and primorial effects."""
from cert import F, mesh, bracket, H, ln_bounds, exp_bounds, rup, ehi, power_coeff, rounded_weights
from math import isqrt

scale=10**30
def clip(a,b):
    return -rup(-a,scale),rup(b,scale)

def ratlog(a):
    return clip(*ln_bounds(a))

def gamma(n=50000):
    q=sum(scale//j for j in range(1,n+1))
    l,u=ratlog(n)
    lower=F(q,scale)-u-F(1,2*n)
    upper=F(q+n,scale)-l-F(1,2*n)+F(1,n*n)
    return lower,upper

def pi_bound(n=10):
    def S(t,n):
        return sum((-1)**j*t**(2*j+1)/(2*j+1) for j in range(n))
    assert n%2==0
    v=F(1,5);w=F(1,239)
    return (16*S(v,n)-4*S(w,n+1),16*S(v,n+1)-4*S(w,n))

def second_weights():
    y=F('28.7296');Y=F('28.7297');Ly=F('3.358')
    a,b=ln_bounds(H)
    assert y<a<b<Y and ln_bounds(Y)[1]<Ly
    out=[]
    for s in mesh:
        c,d=bracket(s);r=(8*s-5)/3;q=5-2*s
        # Improve log-tangent integral via positive quartic Taylor majorant
        # for (1+u)^q (q in [3.25,3.6]); fifth derivative negative.
        assert 3<q<4
        A=F(0); prod=F(1)
        for j in range(5):
            A+=prod/((1+r)**(j+1)*y**j)
            prod*=q-j
        val=4*(c*ehi(-r*y)*ehi(q*Ly)*A+
               d*ehi(-y)*(Y**2/2+Y/2+F(1,4)))
        v=rup(val,10**8)
        if out:v=min(v,out[-1][1])
        out.append((s,v))
    return out

def spectral_g(t,w,rebased=False):
    # Unscaled high-ordinate sum with a factor H pulled out;
    # rebased=True compares to exp(-t/2), rather than exp(-t/8).
    a=F('.5') if rebased else F('.875')
    return (160*ehi((F('.7')-a)*t) + w[-1][1]*ehi((F('.875')-a)*t)
        + sum((u-v)*ehi((s-a)*t) for (_,u),(s,v) in zip(w,w[1:])))

def q(t):
    return (t+2)/(t*(t+1))

def recentered_coeff(L,w):
    qw=q(L); em=ehi(-3*L/8)
    small=(1+2*qw/14)*F('.0463')*em + 2*(1+qw)*ehi(-7*L/8)
    big=(1+2*qw/H)*spectral_g(L,w)/H
    cth=F('.01955')
    # |d| <= cth*exp(-L/8)<10^-12. f(d)= d-L log(1+log(1+d)/L)
    # <= (1+1/L)*.50001 d^2 by Taylor & directed bounds.
    loc=F('.50001')*(1+1/L)*cth**2*ehi(-L/8)
    primepowers=(2*F('1.000000147')+F('2.67')*ehi(-L/6))*em
    minus=(1+1/L)*(small+big)+L*ehi(-7*L/8)
    plus=minus+(1+1/L)*primepowers+loc
    return minus, plus/(1-plus*ehi(-L/8)/L)

def verify():
    p0,p1=pi_bound()
    a,g=gamma()
    assert 2+g-ln_bounds(4*p0)[0]<F('.0463')
    assert ln_bounds(2*p1)[1]<2 and ln_bounds(2*p0)[0]>1
    t=ln_bounds(H)[1]; assert (t*t+2*t+2)/6+2<160
    assert F('.01955')*ehi(-F(190,8))<F('1e-12')
    w=second_weights()
    assert spectral_g(F(190),w)/H<F('4.49e-15')
    assert spectral_g(F(400),w)/H<F('3.20e-15')
    L=F(110); q0=q(L)
    smooth_tail=(F('.0463')*(1+2*q0/14)*ehi(-L/2)
                 +(1+2*q0/H)*spectral_g(L,w)/H*ehi(-L/8)+2*(1+q0)*ehi(-L))
    J=(2*F('1.000000147')+F('2.67')*ehi(-L/6))*ehi(-L/2)
    assert 116*ehi(-L/2)+(1+1/L)*(J+smooth_tail)<F('.01')*F('1.048e-12')
    assert F('.06')*ehi(-F(215,8))<F('1e-12')
    assert F('.04')+F('.01955')*(1+F(7,8)*F('.04')*ehi(-F(215,8)))<F('.06')
    for L,neg,pos in [(190,'4.6e-15','1.5e-14'),(215,'4.6e-15','4.6e-15'),(400,'3.22e-15','3.22e-15')]:
        m,M=recentered_coeff(F(L),w)
        print("primorial scaled endpoint",L,float(m),float(M))
        assert m<F(neg) and M<F(pos)
    # Smooth lower bound on [8,84.5] in units exp(-L/2)/L.
    pts=list(map(F,[8,30,60,70,75,80,83,84,'84.5']))
    for u,v in zip(pts,pts[1:]):
        qw=q(u)
        gap = (F('.9999')*(2-4*qw) - (1+2*qw/14)*F('.0463')
               - (1+2*qw/H)*spectral_g(v,w,True)/H
               - 2*(1+qw)*ehi(-u/2))
        assert gap>0
        left=(1+1/v)*gap-u*ehi(-u/2)
        print("primorial positive cell",float(u),float(v),float(left))
        assert left>F('.10')
    verify_small(a,g)

def verify_small(gn,gu):
    N=3000
    assert exp_bounds(8)[1]<N
    comp=bytearray(N+1)
    a=b=c=d=F(0) # log Q lower/upper, theta lower/upper
    for p in range(2,N+1):
        if comp[p]: continue
        for k in range(p*p,N+1,p): comp[k]=1
        l,u=ratlog(F(p,p-1)); L,U=ratlog(p)
        a+=l;b+=u;c+=L;d+=U
        if p==2:
            assert d<1
            continue
        x,y=ratlog(c)[0],ratlog(d)[1]
        assert x>0
        norm=ratlog(y)[1]
        margin=a-gu-norm
        lower_sqrt=F(isqrt(p*10**16),10**8)
        assert margin > F('.10')/(lower_sqrt*L), (p,float(margin))
    print("all small primorials certified")

def small_mertens():
    M0=3000
    comp=bytearray(M0+1)
    ps=[]
    for p in range(2,M0+1):
        if comp[p]: continue
        ps.append(p)
        for k in range(p*p,M0+1,p): comp[k]=1
    D={p:(ratlog(p),ratlog(F(p,p-1))) for p in ps}
    gl,gh=gamma()
    vl=sum(D[p][1][0]-F(1,p) for p in ps)
    vh=sum(D[p][1][1]-F(1,p) for p in ps)+F(1,M0)
    ml,mh=gl-vh,gh-vl
    bl=gl+sum(D[p][0][0]/(p*(p-1)) for p in ps)
    bh=gh+sum(D[p][0][1]/(p*(p-1)) for p in ps)+(ratlog(M0+1)[1]+1)/M0
    ql=qh=V=wl=wh=F(0)
    counts=0
    def verify_cell(a,b,r=0):
        nonlocal counts
        la,lb=ratlog(a)[0],ratlog(b)[1]
        lla,llb=ratlog(la)[0],ratlog(lb)[1]
        sb=F(isqrt((b*10**30).__floor__())+1,10**15)
        q=F("2.4")/(sb*lb)
        sl=ratlog(1+q)[0]
        if (max(gh+llb-ql,qh-gl-lla)<sl and max(mh+llb-V,V-ml-lla)<q
               and max(lb-wl-bl,wh+bh-la)<F("2.4")/sb):
            counts+=1
        else:
            assert r<12, (a,b)
            m=(a+b)/2
            verify_cell(a,m,r+1);verify_cell(m,b,r+1)
    for a,b in zip(ps,ps[1:]):
        if a>=1000:break
        L,Q=D[a]
        ql+=Q[0];qh+=Q[1];V+=F(1,a)
        wl+=L[0]/a;wh+=L[1]/a
        verify_cell(F(a),F(min(b,1000)))
    print('small Mertens cells',counts)

if __name__=='__main__':
    verify()
    small_mertens()
