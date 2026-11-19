
#!/usr/bin/python3.10
"""Directed, integer-only interval checker for the scalar inequalities.
Run: /usr/bin/python3.10 check.py. No external data/dependencies."""

from fractions import Fraction as F
from math import factorial as fac
from functools import lru_cache
S=10**60

def ceil(n,d): return -((-n)//d)

class I:
    __slots__=('a','b')
    def __init__(self,a,b=None):
        if isinstance(a,I): self.a,self.b=a.a,a.b; return
        if b is None:
            f=F(a); self.a=f.numerator*S//f.denominator
            self.b=ceil(f.numerator*S,f.denominator)
        else:
            self.a,self.b=a,b
    def __add__(x,y): y=I(y); return I(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __neg__(x): return I(-x.b,-x.a)
    def __sub__(x,y): return x+-I(y)
    def __rsub__(x,y): return I(y)+-x
    def __mul__(x,y):
        y=I(y)
        if x.a>=0 and y.a>=0: return I(x.a*y.a//S,ceil(x.b*y.b,S))
        c=[i*j for i in (x.a,x.b) for j in (y.a,y.b)]
        return I(min(c)//S,ceil(max(c),S))
    __rmul__=__mul__
    def inv(x):
        assert x.a*x.b>0
        return I(S*S//x.b,ceil(S*S,x.a))
    def __truediv__(x,y): return x*I(y).inv()
    def __rtruediv__(x,y): return I(y)*x.inv()
    def __pow__(x,n):
        assert isinstance(n,int)
        if n<0: return x.inv()**(-n)
        if not n: return I(1)
        if n==1: return x
        z=x**(n//2); z=z*z
        return z*x if n%2 else z

def rng(a,b): return I(I(a).a,I(b).b)
def lt(a,b): return I(a).b<I(b).a
def approx(a): return a.a/S,a.b/S  # diagnostics only, never used by assertions
def less(a,b):
    assert lt(a,b),(approx(I(a)),approx(I(b)))

@lru_cache(maxsize=80000)
def exp_point(q): # output encloses exp(q/S)
    if q<0: return exp_point(-q).inv()
    r=1
    while 2*q>S*r: r*=2
    z=I(q//r,ceil(q,r))
    p=series=I(1)
    for k in range(1,49):
        p=p*z/k
        series+=p
    series+=I(0,1)  # 2(1/2)^49/49! < 1/S
    while r>1: series*=series; r//=2
    return series

def exp(z):
    z=I(z)
    return I(exp_point(z.a).a,exp_point(z.b).b)

def atanh_log(v):
    assert 0<=v.a and v.b<=S//3+2
    p=v; w=v*v; r=I(0)
    for k in range(1,160,2):
        r+=p/k
        p*=w
    return 2*r+I(0,1) # 2*(1/3)^161/(161*(1-1/9)) < 1/S

LN2=atanh_log(I(F(1,3)))
@lru_cache(maxsize=10000)
def log_point(a):
    assert a>0
    if a<S:
        t=I(a,a).inv()
        return -I(log_point(t.a).a,log_point(t.b).b)
    k=0; b=S
    while a>=2*b: k+=1; b*=2
    return k*LN2+atanh_log(I(F(a-b,a+b)))
def log(a):
    a=I(a)
    return I(log_point(a.a).a,log_point(a.b).b)
def powr(a,b): return exp(log(a)*b)
def sqrt(a): return powr(a,F(1,2))

def arctan_unit(d):
    return sum((I(F((-1)**j,(2*j+1)*d**(2*j+1)))
                for j in range(100)),I(0))+I(-1,1)
PI=16*arctan_unit(5)-4*arctan_unit(239)

# Density bound, using the literal FKS Cor. 2.9 and rounded-up constants.
H0=3*10**12
a=log(H0)
def density_at(s,c1,c2):
    p=I(F(8,3))*(1-s); q=5-2*s
    return 2*c1*exp((p-1)*a+q*log(a))/(1-p-q/a)+2*c2*(a*a+2*a+2)/H0
def dens(L):
    return I('.0106')*L/(L-92)+651*exp(-I(F(3,40))*L)+I('.05')*L*L*exp(-L/8)+I('12.546')*L*exp(-3*L/8)

def check_density():
    less(density_at(I('.75'),I('7.8'),I('4.11')),651)
    less(density_at(I('.875'),I('11.08'),I('3.70')),'.0106')
    less(8*a/3+2*log(a)+(I(F(8,3))+2/a)/(1-I(F(8,15))-I('3.4')/a),92)
    less(dens(I(185)),'.022')
    less(dens(I(200)),'.020')
    # Coefficient extraction for 2(S0+B1(100,V)) in FKS.
    c=1/(2*PI)+(I('.137')*log(100)+I('.443'))/(100*log(100)*log(100/(2*PI)))
    v=I('.5922435112'); r=I('.137')*log(100)+I('.443')*log(log(100))+I('1.588')
    less(2*c,'.322')
    less(2*(v+2*r/100),2)
    less(log(10/(2*PI)),1)
    # 2+.322*(L/2)*(L/4+1)<.05 L^2 for L>=185 (divide by L^2).
    less(I(2)/185**2+I('.322')/8+I('.322')/(2*185),'.05')
    # Density-free fallback using S and FKS 3.2 at T=64*x^(1/8).
    Z=I(185); w=Z/8+log(158)
    less(64*exp(Z/8), (exp(Z/2)-2)/5)
    less(Z,64*exp(Z/8))
    less(2+I('.322')*w*(w/2+1)+I('2.091')*Z/64,I('.0045')*Z**2)
    print('density and density-free constants checked')

TS=[4*10**7,7*10**7,10**8,15*10**7,2*10**8,3*10**8,5*10**8,
    10**9,3*10**9,10**10,3*10**10,10**11,3*10**11,10**12,3*10**12]
AT=[I('3.142')/T for T in TS]
BT=[(log(T/(2*PI))**2-log(T/(2*PI))/3)/(2*PI) for T in TS]
# use the exact Cor. 1.2 B_T, inflated to a hundredth
BT=[I(F(ceil(t.b*100,S),100)) for t in BT]
C=199584000
CP=I('.15'); K=I('2.06')
N=10
B=[sum(fac(k)*fac(n-k) for k in range(max(0,n-N),min(N,n)+1)) for n in range(2*N+1)]
A=[sum(fac(n)//fac(j) for j in range(n+1)) for n in range(N+1)]
D=[A[n]-B[n] for n in range(N+1)]

def r0(z,j,upper):
    A0,B0=AT[j],BT[j]+I('-.99' if upper else '1.43')
    return A0*(1+2/z)+B0*(1+3/z)*exp(-z/2)+(100000*A0+100*B0+50)*z*exp(-z)

def rh(z):
    return (z*z/64+z/56)*exp(-z/8)+I('1.43')*(1+3/z)*exp(-z/2) + (I('6e-17')*exp(200-z)+3*exp(-z))*z
def rd(z):
    return I('.022')*(1+I('1.16')/z)*exp(-z/8)+I('1.43')*(1+3/z)*exp(-z/2)+(I('7e-17')*exp(185-z)+3*exp(-z))*z

def rn(z):
    return I('.0045')*(z*z+8*z/7)*exp(-z/8)+I('1.43')*(1+3/z)*exp(-z/2)+(I('7e-17')*exp(185-z)+3*exp(-z))*z

def choose(vals):
    return min(vals,key=lambda x:x.b)
def r(z,upper,dense):
    rs=[r0(z,j,upper) for j in range(len(TS))]
    if dense in (False,'both') and z.a>=200*S: rs.append(rh(z))
    if dense in (True,'both') and z.a>=185*S: rs.append(rd(z))
    if dense=='nondensity' and z.a>=185*S: rs.append(rn(z))
    if upper and z.b <= 3932*S//100: rs.append(2*z*exp(-z))
    return choose(rs)
def poly_lower(z):
    return sum(D[n]/z**(n-4) for n in range(4,11))-sum(B[n]/z**(n-4) for n in range(11,21))
def loss(z,dense):
    return K*(C/z**7+CP*z**5*exp(15-z)+z**4*r(z,True,dense)) + CP*z**5*exp(16-z) + z**5*r(z-1,False,dense)/(z-1)

def check_ram_constants():
    for T,t in zip(TS,AT):
        less(PI/(T-1)+PI*PI/(3*T*T),t)
    less(exp(I('39.32')),120000000000000000)
    # Prefix integrals as upper Riemann sums in log coordinates.
    for h,n in [(I(1),100000),(I('.5'),100)]:
        f=(exp(h)-exp(h*LN2))/(h*LN2**2)
        f+=sum((exp(h*(k+1))-exp(h*k))/(h*k*k) for k in range(1,16))
        less(f,n)
    less(2/LN2+22/(LN2**2),50)
    # Li anchor and upper bound used in the squared expression.
    less(I(2)/15+exp(I('-7.5'))/LN2,'.15')
    less(sum(fac(k)/I(15)**(k+1) for k in range(11)),'.15')
    for z,target in [(185,I('7e-17')),(200,I('6e-17'))]:
        Z=I(z)
        # prefix integral, divided by exp(z)
        less(AT[-1]*(2/Z**2+100000*exp(-Z)) +
             I('115.1')*(3*exp(-Z/2)/Z**2+100*exp(-Z)),target)
    Z=I('36.96')
    F0=sum(fac(k)/Z**k for k in range(11))
    less(2*F0+C/Z**11+CP*Z*exp(15-Z)+r0(Z,2,True),'2.06')
    # Strict positivity of the lower pi estimate is not needed for R.
    print('Ramanujan constants checked')

def check_finite_ram():
    # 1/50 mesh: the intervals, not just their endpoint values, are checked.
    # Choose lower targets progressively; maintain one H-only full ray.
    for a,b,tag in [(1848,2150,'low'),(2150,15000,'unit'),
                      (2150,15000,'unit_nd'),
                      (2550,15000,'slope'),(11800,15000,'quad')]:
        worst=I(100); arg=0
        for j in range(a,b):
            L=rng(F(j,50),F(j+1,50))
            if tag=='low': target=I('.05'); dense=False
            if tag=='unit': target=I(1); dense=False
            if tag=='unit_nd': target=I(1); dense='nondensity'
            if tag=='slope': target=1+I('13.8')/L; dense=True
            if tag=='quad': target=1+14/L+145/L**2; dense=True
            gap=poly_lower(L)-loss(L,dense)-target
            if gap.a<worst.a: worst,arg=gap,j
            if gap.a<=0: raise AssertionError((tag,j,approx(gap)))
        print('Ramanujan',tag,'certified; worst lower surplus',approx(worst)[0],'at',F(arg,50))

def check_ray_ram():
    # For L>=300, L^j e^-cL decreases coefficientwise in the proof (j<=8,
    # shifted powers or rational factors are covered in the text).
    Z=I(300)
    # Here use the direct tail models even if other choices happen to be better.
    for f,k,pay in [(rh,1,14),(rn,1,14),(rd,3,1412),(rd,4,13985)]:
        loss0=K*(C/Z**7+CP*Z**5*exp(15-Z)+Z**4*f(Z)) + CP*Z**5*exp(16-Z) + Z**5*f(Z-1)/(Z-1)
        t=sum(B[n]/Z**(n-4) for n in range(11,21))
        less((loss0+t)*Z**k,pay)
    print('Ramanujan infinite tails checked')


def check_mertens():
    # Euler constant elementary enclosure; the arithmetic is directed.
    n=10000
    gamma=sum((I(1)/j for j in range(1,n+1)),I(0))-log(n)-I(1)/(2*n)
    gamma=gamma+I(0,ceil(S,n*n))
    less(gamma,'.577216')
    less(2+gamma-log(4*PI),'.0462')
    less(log(2*PI),'1.84')
    def B5(t):
        return (1+log(t/(2*PI)))/(2*PI*t)+(I('.4')*log(t)+I('4.1'))/t**2
    less(2*B5(H0),'3.1e-12')
    L=log(5000000); u=L/2; eps=I('20.83')/u**3
    yh=sqrt(5000000)
    J0=I('.0462')+I('3.1e-12')*powr(10**13,F(3,8))+I('1.84')/yh
    c=(1-eps)*(1-1/u+2/u**2-6/u**3-1/(2*yh))-eps
    less(I('.003')+I('.751')+(1+1/L)*J0,c)
    less(I('.1')+I('.751')+J0,1-2*eps)
    eta=I('.000081')
    less(I('.5')*(1+eta)+eta+I('20.83')/(L/3)**3,'.66')
    less(2*(1+eta)+(1+eta)*4/(3*(1-exp(-L/4))),'3.37')
    n=10**8; A=log(n); B0=log(10**13)
    e=I('20.83')/(A/2)**3
    W=1+2*eta+e+I('.66')*exp(-A/6)+I('3.37')*exp(-A/4)
    less(W,'1.092')
    j=I('.0462')+I('3.1e-12')*exp(3*B0/8)+I('1.84')*exp(-A/2)
    less(I('.791')+(1+1/A)*j+W,'1.94')
    # Finite to analytic transition. Test monotone upper functions at left ends.
    def relcap(coef, l, bound):
        less(coef/(1-coef/l**3),bound)
    relcap(I('1.94')*A**2*exp(-A/2),A,'.067')
    jB=I('.0462')*exp(-B0/2)+I('3.1e-12')*exp(-B0/8)+I('1.84')*exp(-B0)
    cB=I('1.048e-12')*200**2+(I('113.67')+W)*B0**2*exp(-B0/2)+(B0**2+B0)*jB
    relcap(cB,B0,'.034')
    Z=I(200)
    units=(1+1/Z)*(I('.0462')*exp(-3*Z/8)+I('3.1e-12')+I('1.84')*exp(-7*Z/8))+W*exp(-3*Z/8)
    cH=(Z*Z/64+units)*Z**2*exp(-Z/8)
    relcap(cH,Z,'.00036')
    less(dens(Z)+units,'.01985')
    less(I('.01985')/(1-I('.01985')*exp(-Z/8)/Z),'.019851')
    for start,m,k in [(2278382,'0.19998','.199995'),(2300000,'.19850','.19852'),
                      (5000000,'.15020','.15021'),(10**7,'.11970','.11971'),
                      (2*10**7,'.08880','.08881'),(3*10**7,'.08820','.08821'),
                      (5*10**7,'.07110','.07111')]:
        relcap(I(m),log(start),k)
    Nt=I(n)
    # Finite constants used in sieve.c: W-tail and C-tail.
    wt=(1+3*I('20.83')/log(n)**3)/(1-1/Nt)
    less(wt,'1.02')
    less(wt/(2*log(n)),F(1,12))
    print('Mertens analytic and finite-cert scalar constants checked')

def check_short():
    # h=half the interval length, T=2.1 x/h. Case A is the pure-log
    # multiplier, case B gains loglog(x)^3.
    for Z,k,b in [(240,210000,0),(300,1050,3)]:
        Z=I(Z); z=log(Z); a0=3*Z/8-I('12.75')*z+log(k)+b*log(z)
        less(30,a0)
        less(log(k)+b*log(z),I('12.75')*z)
        # 4c1/(2-p-q/a). Use a0 as the smallest possible a.
        d=4*I('11.08')/(2-I(F(16,15))-I('3.8')/a0)
        less(4*I('5.30')/(2-2/a0),11)
        # normalized by (log L) if b=3. Below takes a<=3L/8.
        den=32*z-I(F(8,3))*log(k)-I(F(8*b,3))*log(z)
        if b==3: den=den/z
        high=d*powr(I('.375'),F(13,4))*powr(k,F(1,3))/den
        lo=4*k*(3*Z/8+1)*exp(-Z/40)*powr(Z,F(-51,4))*z**b
        sec=11*(3*Z/8)**2*exp(-Z/8)
        # x+2h<1.01x, so prime powers cost <1.44 sqrt(x)/h.
        interval_rel=I('4.2')/k*exp(-3*Z/8)*powr(Z,F(51,4))/z**b
        less(interval_rel,'.01')
        pp=I('2.88')*k/I('4.2')*exp(-Z/8)*powr(Z,F(-51,4))*z**b
        less(high+lo+sec+pp,'.934' if b==0 else '.822')
        less(1/(exp(Z)*(exp(2*Z)-1)),'.001')
        print('short interval case',b,'scalar loss upper',approx(high+lo+sec+pp)[1])
    # Pointwise theta: length .041 x^(7/8) is available from L>=200.
    Z=I(200)
    c=I('.041')
    eps=I('.020')
    V=eps+I('1.43')*exp(-3*Z/8)
    less(V*(1+powr(1+c*exp(-Z/8),F(7,8))),'.04001')
    # Short interval is smaller than original x/(5000 L^2).
    for Z,k,b in [(240,210000,0),(300,1050,3)]:
        Z=I(Z)
        less(5000*I('4.2')/k*exp(-3*Z/8)*powr(Z,F(59,4))/log(Z)**b,1)
    # Cube application (short interval is shorter than 3x^(2/3)).
    Z=I(2060)
    less(I('2e-5')*powr(Z,F(51,4))*exp(-Z/24),3)
    less(5000*I('.041')*(I(200)**2)*exp(-I(25)),1)
    Z=I(200)
    uu=I('.020')+I('1.43')*exp(-3*Z/8)+(Z+LN2)*exp(-7*Z/8)
    less(uu,'.02001')
    dk=I('.02001')*exp(-Z/8)
    s=dk/(1-dk)
    less(I('.019851')+I('.02001')/(1-dk)/(1-s/Z),'.041')
    # Conversion of p to X=log N incurs only this tiny factor.
    less(I('.041')*powr(1+dk,F(1,8))*(1+s/Z),'.042')
    print('short interval and extremal totient scalar certificates passed')

if __name__=='__main__':
    check_density()
    check_ram_constants()
    check_ray_ram()
    check_mertens()
    check_short()
    check_finite_ram()
