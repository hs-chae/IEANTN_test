"""Additional exact analytic-region checks (Python 3.10)."""
from fractions import Fraction as F
from math import isqrt, factorial
from ray_check import up,lu,aa,bb,A,grid,loss,TAIL,dcoeff,C2

def high_unconditional():
    R=F('5.573412')
    L=F(2834)
    U=F(4000)
    c=F('0.9926')
    p=F(8,3)*(1-c)
    q=5-2*c
    z,Z=lu(3*10**12)
    z0=F('28.729')
    assert z0<z and U<R*z0*z0 and L>4*R*80
    _,l3=lu(3)
    _,l80=lu(80)
    _,lZ=lu(Z)
    assert up((q-3)*l80)<F('1.07')
    assert F(8,3)*(F('28.8')+F('1.1'))+2*F('3.37')+(F(8,3)+2/F('28.7'))/(1-F(8,30)-F('3.2')/F('28.7'))<95
    c0=F('9.8')*up(p*l3)
    # Rigorous upper integration on the entire rectangle range.
    I=F(0)
    for l,r in grid(z0,F(80),F(1,100)):
        I+=(r-l)*(c0*F('1.07')*r**3*up((p-1)*l)+103*r*r*up(-l))*up(-L/(R*r))*(1-L/(R*r*r))
    tail=(c0*80**4*up((p-1)*80)/(1-p-F(4,80))
          +103*80**2*up(-80)/(1-F(2,80)))
    wc=(c0*up(q*lZ+(p-1)*z)/(1-p-q/z)
        +103*Z**2/(3*10**12*(1-2/z)))
    lowpart=500*up(-L/10)+wc*L/(L-95)*up(-(1-c)*L)
    K=F('0.321')
    assert L**4*(I+lowpart)+U**4*(tail+3*up(-L/2))+F('2.091')*U**5*up(-54)<K
    ky=isqrt(4000*10**12)
    sl,su=F(ky,10**6),F(ky+1,10**6)
    assert F('9.22022')*U**5*su*up(-F('0.8476836')*sl)+3*U**4*up(-U/2)<K
    # Bound normalized pi loss on all L>=2839.
    l=L+5
    scaled=(K+K/(l-12)+4*A*l**3*up(-5)
            +F(9,4)*l**5*(A*up(-l/2)+234*up(-3*l/4))
            +(936*l**3+117*l**4)*up(-l/2)+3*l**5*up(-l))
    # Add the a priori Li_2 remainder for approximation as in candidate.md.
    from math import factorial
    scaled+=F(4*factorial(13))/l**9+2*l**5*up(-3*l/4)
    start=l+1
    assert scaled< F('0.322')
    assert TAIL/start**9+scaled*((start/(start-1))**5+2+4/start+scaled/start**4)<F('0.97')
    print("unconditional Ramanujan ray [2840,infinity) passed")
    # Also close the unconditional mid-range gap as far as the CH2
    # constant majorant allows without a new technique.
    for l,r in grid(F(169),F(753),F(1,2)):
        val=1+14/r+145/r**2+1412/r**3-TAIL/l**9
        assert val-r**4*loss(l,r,'C')>F('0.004'),(l,r)
    print("unconditional Ramanujan intermediate interval [169,753] passed")

def signed_small_ramanujan():
    lo,hi=F('37.5'),F('39.45')
    assert up(hi)<F('1.39e17')
    k=sum(F(C2[n],36**(n-13)) for n in range(13,25))
    def rem(l,r):
        return F(4*factorial(13))/l**13+2*r*up(-3*l/4)
    for l,r in grid(lo,hi,F(1,100)):
        m,M=l-1,r-1
        a=(M*M+2*M)*up(-m/2)/25+1350*M*up(-m)+rem(m,M)
        b=3*r*up(-l)+rem(l,r)
        d=1+14/r+145/r**2+1412/r**3-k/l**9
        assert d-r**4*(l*a/(l-1)+(2+4/l+b)*b)>F('.1'),(l,r)
    print("signed small Ramanujan interval [37.5,39.45] passed")

def oscillatory():
    s=F('0.77')
    p=F(8,3)*(1-s); q=5-2*s
    _,l3=lu(3)
    l=F(200)
    z=l/3
    _,lz=lu(z)
    Ahi=(F('9.8')*up(p*l3+q*lz+(p-1)*z)/(1-p-q/z)+103*z*z*up(-z)/(1-2/z))
    c1,c2,c3,d1,d2,d3=(F('0.02'),F('2.091'),F(3),F('.23'),F(1,3),F(1,2))
    kscaled=c1*l*l*up(-(d1-aa)*l)+c2*l*up(-(d2-aa)*l)+c3*up(-(d3-aa)*l)+Ahi
    assert kscaled< F('.001065')
    # Bound the oscillatory integral and boundary error at L>=200.
    # Monotonicity of each scaled envelope then gives uniform constants.
    theta=dcoeff(l)+3*up(-(F(1,2)-aa)*l)
    # effective exponential damping >= a for all remainder terms
    j=kscaled/aa
    zp=theta+(1+1/l)*(2*F('0.119')*l/(l-97)/(3*10**12)+j)+l*up(-(1-aa)*l)
    zz=zp*up(-aa*l)/l
    assert zp/(1-zz)<F('0.24')
    # Improved absolutely convergent inverse-square spectral weight.
    b=bb
    p=F(8,3)*(1-b)
    q=5-2*b
    z,Z=lu(3*10**12)
    _,lz=lu(Z)
    m2=F('19.6')*up(p*l3+(p-2)*z+q*lz)/(2-p-q/z)+206*Z**2/((3*10**12)**2*(2-2/z))
    assert m2 < F('2.51e-14')
    v=(1+1/l)*(F('2.51e-14')*l/(l-97)+j) + (1/l+2/l**2)/aa*F('2.51e-14')*l/(l-97)
    v+=l*up(-(1-aa)*l)+2*theta**2*up(-aa*l)
    assert v/(1-v*up(-aa*l)/l) < F('.0069')
    assert theta<F('.232')
    assert F('.465')-2*F('.232')-bb*F('.232')*F('.465')*up(-aa*l)>F('.000999')
    assert up(-aa*l)*F('.465')<F('.1')
    print("oscillation-aware Mertens .24 constants passed")

if __name__=='__main__':
    high_unconditional()
    oscillatory()
    signed_small_ramanujan()
