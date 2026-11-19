"""Directed certificates for the shared analytic zero-density bounds."""
from fractions import Fraction as Q
from functools import lru_cache
from ram_repair import logb, series, pl, pu
from d01_cert import bracket, mesh
H=3000175332800
q=Q('1.047136353e-12')
CT=Q('113.669378')
D=Q(5,32)
D0=Q(1,8)
S0=Q('.70')
M=10**270
def up(r,M=M):return Q((M*r).__ceil__(),M)
def down(r,M=M):return Q((M*r).__floor__(),M)
ee,EE=map(Q,series(Q(1),190))
ee,EE=down(ee,10**345),up(EE,10**345)
@lru_cache(None)
def intpow(n):
    if not n:return Q(1),Q(1)
    a,b=intpow(n//2)
    return down(a*a*(ee if n%2 else 1)),up(b*b*(EE if n%2 else 1))
@lru_cache(None)
def ep(t):
    t=Q(t)
    if t<=-630:
        assert ee**630>M
        return Q(0),1/Q(M)
    if t<0:
        a,b=ep(-t)
        return down(1/b),up(1/a)
    n=t//1
    a,b=series(t-n,32)
    v,w=intpow(n)
    return down(v*a),up(w*b)
def eu(t):return ep(t)[1]
def el(t):return ep(t)[0]

@lru_cache(None)
def nodes(d):
    b=1-d
    return sorted({s for s in set(mesh)|{Q(27,32)}|{Q(27,32)-Q(k,10**j) for j in range(3,8) for k in range(1,10)} if s<b} | {b}
                  | {b-Q(k,10**j) for j in range(3,8) for k in range(1,10)
                     if b-Q(k,10**j)>S0})
@lru_cache(None)
def W(s,m):
    # w_1 majorizes sum 1/|gamma|; w_2 majorizes H*sum 1/gamma^2.
    c,d=bracket(s)
    r=m-Q(8,3)*(1-s); p=5-2*s
    z,Z=logb(Q(H))
    z,Z=down(z,10**16),up(Z,10**16)
    L=up(logb(Z)[1],10**16)
    a=Q(0); f=Q(1)
    assert r>0 and 3<p<4
    for j in range(5):
        a+=f/z**j/r**(j+1)
        f*=p-j
    upper=2*m*(c*eu(-((8*s-5)/3)*z)*eu(p*L)*a
                 + d/H*(Z*Z/m+2*Z/m**2+Q(2,m**3)))
    # Near H, N(s,T) <= N(T)-N(H), since s>1/2 and RH through H.
    # Replace a short initial portion of the density integral by this
    # overall count. Try dyadic eta in [2^-16, 2] independently at each s.
    base=c*el(-((8*s-5)/3)*Z)*el(p*down(logb(z)[0],10**16))
    from ram_repair import logb as ilog
    w=ilog(2*pl)[0]
    saving=Q(0)
    for j in range(-16,2):
        eta=Q(2)**j
        reduced=base*(1-eu(-r*eta))/r
        total=(Z+eta-w)/(2*pl)*eta**2/2+(Q(2,5)*Z+eta/5+4)/H*eta
        saving=max(saving,2*m*(reduced-total))
    assert 0<=saving<upper
    return up(upper-saving,10**11)

@lru_cache(None)
def mass(d,m):
    v=[]
    for s in nodes(d):
        w=W(s,m)
        v.append((s,min(v[-1][1],w) if v else w))
    return v
def spectral(L,d,m,E=eu):
    v=mass(d,m)
    return v[-1][1]+sum((w-z)*E((s-1+d)*L) for (_,w),(s,z) in zip(v,v[1:]))
@lru_cache(None)
def F(L,d=D):
    assert L>=40
    return (((L/3+1)**2/6+2)*eu(-(1-S0-d)*L)
            +Q('2.091')*L*eu(-(Q(1,3)-d)*L)+spectral(L,d,1))
@lru_cache(None)
def J(L,d=D):
    assert L>=18
    return (13*eu(-(1-S0-d)*L)+spectral(L,d,2))/H
def psi(L,d=D):return F(L,d)*eu(-d*L)
def theta(L,d=D):return psi(L,d)+Q('1.000000147')*eu(-L/2)+Q('1.78')*eu(-2*L/3)
def checks():
    # Legal FKS height and sum estimate. log(2.45/(2pi))<0.
    assert el(Q(40,3))>51 and el(Q(40,3))>40
    assert el(Q(40,6))>5+2*eu(-Q(40,3))
    assert Q('2.45')<2*pl
    assert 1/(2*pl)<Q(1,6)
    n=1000
    gamma_upper=sum(Q(1,k) for k in range(1,n+1))-logb(Q(n))[0]-Q(1,2*n)+Q(1,n*n)
    assert 2+gamma_upper-logb(4*pl)[0]<Q('.0463')
    assert 1<logb(2*pl)[0]<logb(2*pu)[1]<2
    assert 1+1/(Q('.7')-2/Q('29.9'))<Q('2.6')
    # For the crude reciprocal-square bulk: integrate
    # 2 int_H^infty ((log t)^2/6+2)/t^2 dt.
    z=logb(Q(H))[1]
    assert (z*z+2*z+2)/3+4 < 310
    # Sharper use |gamma|>H, subtract low cumulative reciprocal sum.
    # Both-sign count-weight error is <=3.7284.
    assert (2*logb(Q(H)/(2*pl))[1]+2)/(2*pl)+Q('3.7284') < 13
    assert el(Q(40))>max(H,10**9) and pu/H+(pu/H)**2<q
    l=logb(H/(2*pu))[0];u=logb(H/(2*pl))[1]
    assert (u*u-u/3)/(2*pl)<CT and l>1
    for d in (D,D0):
        print('strip delta',d,'limit W1, W2/H',float(mass(d,1)[-2][1]),
              float(mass(d,2)[-2][1]/H))
    assert mass(D,1)[-2][1]<Q('.146023')
    for a in (40,140,150,155,160,165,170,180,190,200,250,400,1000):
        L=Q(a)
        print('density',a,*(float(z) for z in (psi(L),F(L),J(L),psi(L,D0))),flush=True)
if __name__=='__main__':checks()
