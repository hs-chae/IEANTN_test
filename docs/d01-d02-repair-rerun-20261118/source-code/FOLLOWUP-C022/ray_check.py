"""Rational certificate for statements on real rays. Python 3.10."""
from fractions import Fraction as F
from math import factorial, comb, isqrt
from functools import lru_cache
from mertens_check import lg, B as SCALE

def epos(x):
    # Choose m so that 0 <= x/m <= 1, truncate exp at j=30.
    x=F(x)
    assert x>=0
    m=max(1,-(-x.numerator//x.denominator))
    # Round a power with a rational interval at each multiply (80 decimal digits).
    K=10**80
    y=x/m
    s=sum(y**j/factorial(j) for j in range(31))
    t=s + F(2,factorial(31))
    lo=(s.numerator*K)//s.denominator
    hi=-((-t.numerator*K)//t.denominator)
    a=b=K
    for _ in range(m):
        a=a*lo//K
        b=-((-b*hi)//K)
    return F(a,K),F(b,K)

@lru_cache(maxsize=None)
def ei(x):
    x=F(x)
    if x>=0:
        return epos(x)
    l,h=epos(-x)
    return 1/h,1/l

def low(x):return ei(F(x))[0]
def up(x):return ei(F(x))[1]
def lu(x):
    x=F(x)
    lo,hi=lg(x.numerator,x.denominator)
    return F(lo,SCALE),F(hi,SCALE)

def atan_interval(inv):
    x=F(1,inv)
    a=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(8))
    return a,a+x**17/17

def pi_interval():
    a,b=atan_interval(5)
    c,d=atan_interval(239)
    return 16*a-4*d,16*b-4*c

pl,ph=pi_interval()
A=F(1048,10**15)
bb=F(27,32)
aa=1-bb
assert pl>F('3.14159') and ph<F('3.14160')
assert ph/(3*10**12)<A and 8*pl>25
assert lu(2)[0]>F(2,3)
assert up(58)<F('2.169')*10**25
assert up(39)<F('1.39')*10**17
assert up(F('29.9'))<10**13 and low(F('18.42'))<10**8
assert lu(10**8)[0]>F('18.42')
assert F('113.67')+F('1.000000147')+F('1.78')*up(-lu(2)[0]/6)<117

def dcoeff(l):
    return (F('0.119')*l/(l-97)+F('0.02')*l*l*up(-(F('0.23')-aa)*l)
            +F('2.091')*l*up(-(F(1,3)-aa)*l))
def spectral_checks():
    z,Z=lu(3*10**12)
    l3,L3=lu(3)
    lz,Lz=lu(Z)
    assert F('28.7')<z<=Z<F('28.8')
    assert L3<F('1.1') and Lz<F('3.37')
    p,q=F(8,3)*(1-bb),5-2*bb
    w=F('9.8')*up(p*L3+(p-1)*z+q*Lz)/(1-p-q/z)
    w+=103*Z**2/(3*10**12*(1-2/z))
    assert w<F('0.119')
    z0=F('28.7')
    s0=F('0.77')
    p0=F(8,3)*(1-s0)
    q0=5-2*s0
    den=1-p0-q0/z0
    assert den>F('0.265')
    assert F(8,3)*(F('1.1')+F('28.8'))+2*F('3.37')+(F(8,3)+2/z0)/den<97
    l100,L100=lu(100)
    llog,Llog=lu(L100)
    r=F('0.137')*L100+F('0.443')*Llog+F('1.588')
    c=1/(2*pl)+(F('0.137')*L100+F('0.443'))/(100*l100*lu(100/(2*ph))[0])
    assert c<F('0.161') and 2*r/100<F('0.06')
    assert 2*F('0.653')/160**2+F('0.161')*F('0.34')**2<F('0.02')
    assert dcoeff(168)<F('0.284')
    assert A*up(aa*168)<F('0.284')
    assert dcoeff(200)<F('0.232')
    assert F('0.232')*2600<200**2/64
    print("spectral constants passed")

C2=[sum(factorial(j)*factorial(n-j) for j in range(13) if 0<=n-j<=12)
    for n in range(25)]
c0=[sum(factorial(j)*comb(n,j) for j in range(n+1))-C2[n]
    for n in range(13)]
assert c0[:8]==[0,0,0,0,1,14,145,1412] and min(c0[8:])>=0
TAIL=sum(F(C2[n],38**(n-13)) for n in range(13,25))
assert TAIL<1_276_000_000

def Ju(s,l,r):
    return up(-(1-s)*l)*(1+1/(s*l-4))+9*r*up(-(1-s/2)*l)/(4*s)
def h(l,r,k):
    c=A*Ju(F(1),l,r)+117*Ju(F(1,2),l,r)+3*r*up(-l)
    if k=='A':
        c=min(c,F('0.284')*Ju(bb,l,r)+117*Ju(F(1,2),l,r)+3*r*up(-l))
    if r<=58:
        c=min(c,up(-l/2)*(r*r+2*r)/25+1350*r*up(-l))
    return c+F(4*factorial(13))/l**13+2*r*up(-3*l/4)
def hu(l,r):
    return F('0.284')*Ju(bb,l,r)+117*Ju(F(1,2),l,r)+3*r*up(-l)+F(4*factorial(13))/l**13+2*r*up(-3*l/4)
def loss(l,r,k):
    a=h(l-1,r-1,k)
    b=h(l,r,k)
    return l*a/(l-1)+(2+4/l+b)*b
def grid(l,r,step):
    while l<r:
        m=min(r,l+step)
        yield l,m
        l=m

def ram_checks():
    # lower coefficient 0.01 on the real domain [39.75,50]
    for l,r in grid(F('39.75'),F(50),F(1,64)):
        val=1+14/r+145/r**2+1412/r**3-TAIL/l**9
        assert val-r**4*loss(l,r,'C')>F('0.01'),(l,r)
    # lower coefficient (1 + 14/L + 60/L^2) from L=50 through L=169.
    # 58 is a partition endpoint and the original finite RH bounds used
    # by h() are only used when the entire cell is within their domain.
    for start,finish,step in [(50,58,F(1,8)),(58,100,F(1,4)),(100,169,F(1,4))]:
        for l,r in grid(F(start),F(finish),step):
            val=85+1412/r-TAIL/l**7
            assert val>r**6*loss(l,r,'C'),(l,r)
    # L^6 times the loss is decreasing on [169,infinity) when using hu
    # separately at L and L-1. (See derivation in candidate.md.)
    l=F(169)
    a=hu(l-1,l-1)
    h0=hu(l,l)
    assert l**6*(l*a/(l-1)+(2+4/l+h0)*h0)<74
    assert 85-TAIL/l**7>74
    print("Ramanujan ray passed")

B0=F('29.9')
L0=F('18.42')
def finite_mertens_checks():
    # Mid-range bound prior to FKS unconditional tail splice.
    aa0=A
    # Power bound from v=3000 using FKS Corollary 1.4 and prime powers.
    K=3000
    k=isqrt(K*10**12)
    xl=F(k,10**6)
    xu=F(k+1,10**6)
    assert (F('9.22022')*K**4*xu*up(-F('0.8476836')*xl)
            +3*K**3*up(-F(K,2)))<F('0.0003')
    # Uniform strong psi/theta majorant used for finite constants.
    assert F('0.751')+F('1.000000147')+F('1.78')*up(-L0/6)<F('1.84')
    assert F('1.84')*up(-L0/2)<F(1,5000)
    assert B0**2*up(-B0/2)/25<F(1,5000)
    assert aa0+117*up(-F(58,2))<F(1,5000)
    # Tail integration on [58,3000] + [3000,infinity).
    Ihi=aa0*(K-58)+234*up(-F(58,2))+F('0.0003')/(2*K*K)
    Jhi=(1+F(1,58))/58*Ihi
    # FRH tail from B0 onwards, beyond the CH2 splice pessimistically added.
    I=up(-B0/2)*(2*B0**2+8*B0+16)/25+Ihi
    J=up(-B0/2)*(2*B0+6)/25+Jhi
    # phi=theta/x-1 is nonpositive in the range in which the first line
    # is used. Lower error from boundary only plus far tail.
    I39=up(-F(39,2))*(2*39**2+8*39+16)/25+Ihi
    J39=up(-F(39,2))*(2*39+6)/25+Jhi
    def e2(l):return F('1.751000147')*up(-l/2)+F('1.78')*up(-F(2,3)*l)
    # I and J prime-counting tails normalized by L^2 or L^3.
    for l,r in grid(L0,B0,F(1,50)):
        i=r**2*(2*F('1.751000147')*up(-l/2)+F('2.67')*up(-F(2,3)*l)+I)
        # w3=(1+v)/v^2. At exponent 1/2, integral <=
        # e^-L/2 (2/L - 2/L^2 + 8/L^3).
        # At exponent 2/3 use I1+I2 <= e^-fL/(fL).
        j=r**3*(F('1.751000147')*up(-l/2)*(2/l-2/l**2+8/l**3)
                 +F('2.67')*up(-F(2,3)*l)/l+J)
        ilo=r**2*(e2(l)+I39)
        jlo=r**3*(e2(l)/l+J39+up(-l))
        assert max(i,ilo)<F('0.135'),(l,r,"V")
        # Conservative conversion exp(z)-1 <= z/(1-z).
        h=max(j,jlo)
        assert h/(1-h/l**3)<F('0.125'),(l,r,"Q")
    # B0 <= L <=58: normalized triangle maxima at B0 for the decaying
    # FRH terms, and 58 for the later tail constants.
    i=(3*B0**2+8*B0+16)*up(-B0/2)*B0**2/25+58**2*Ihi
    j=(3*B0+6)*up(-B0/2)*B0**3/25+58**3*(Jhi+up(-B0))
    assert i<F('0.135') and j/(1-j/B0**3)<F('0.125')
    # 58 <= L <= 3000: use monotonically decreasing exponential times
    # L^2 at 58 and global fixed constant tails.
    u=(aa0+aa0*(K-58)+F('0.0003')/(2*K*K))*K*K+351*58**2*up(-F(58,2))
    assert u<F('0.135')
    # T_3 <= w_3(L) T_2 and B_3 = B_2/L.
    v=(1+F(1,58))*u+58**3*up(-58)
    assert v/(1-v/58**3)<F('0.125')
    # L >= 3000: d <= .0003/L^3.
    u=F('0.0003')*(F(1,K)+F(1,2))
    v=(1+F(1,K))*u+F(1,10**6)  # bound L^3 e^-L using L>=3000
    assert u<F('0.135') and v/(1-v/K**3)<F('0.125')
    print("unconditional Mertens rays passed")

if __name__=='__main__':
    spectral_checks()
    ram_checks()
    finite_mertens_checks()
