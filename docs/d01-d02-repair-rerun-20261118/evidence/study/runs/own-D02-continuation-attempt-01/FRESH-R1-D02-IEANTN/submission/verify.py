"""Reproduce with /usr/bin/python3.10 verify.py [--endpoint]. No non-stdlib dependency."""
from decimal import Decimal as D, getcontext, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction
from math import factorial as fac, comb
import sys

dn=Context(prec=55,rounding=ROUND_FLOOR)
up=Context(prec=55,rounding=ROUND_CEILING)
rn=Context(prec=55,rounding=ROUND_HALF_EVEN)
class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.a,self.b=a.a,a.b; return
        self.a=D(str(a)); self.b=self.a if b is None else D(str(b))
        assert self.a<=self.b
    def __add__(a,b):
        b=I(b);return I(dn.add(a.a,b.a),up.add(a.b,b.b))
    __radd__=__add__
    def __neg__(a):return I(a.b.copy_negate(),a.a.copy_negate())
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b)
        pairs=[(x,y) for x in (a.a,a.b) for y in (b.a,b.b)]
        return I(min(dn.multiply(x,y) for x,y in pairs),max(up.multiply(x,y) for x,y in pairs))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.a>0 or b.b<0
        return a*I(dn.divide(D(1),b.b),up.divide(D(1),b.a))
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,b):
        if type(b) is not int:return (a.log()*b).exp()
        if b<0:return 1/a**(-b)
        if b==0:return I(1)
        if b==1:return a
        if b%2==0:
            t=a**(b//2); return t*t
        return a*a**(b-1)
    def exp(a):return I(rn.next_minus(rn.exp(a.a)),rn.next_plus(rn.exp(a.b)))
    def log(a):
        assert a.a>0
        return I(rn.next_minus(rn.ln(a.a)),rn.next_plus(rn.ln(a.b)))
    def __repr__(a):return '[%s,%s]'%(a.a,a.b)

# Machin identity follows by tangent addition in (0,pi/2).
def atan_inv(k):
    s=sum((Fraction((-1)**j,(2*j+1)*k**(2*j+1)) for j in range(64)),Fraction())
    t=s+Fraction(1,129*k**129)
    return I((I(s.numerator)/s.denominator).a,(I(t.numerator)/t.denominator).b)
pi=16*atan_inv(5)-4*atan_inv(239)
assert pi.a>D('3.14159') and pi.b<D('3.14160')
c=I('1.048e-12')
assert (pi/3000000000000).b<c.a
H=3000000000000
h0=I(H).log()
def g(x):return G(I(x))
def factpoly(x):return sum(fac(j)/x**j for j in range(19))
def G(x):
    return x**4*(x/(x-1)*factpoly(x-1)-factpoly(x)**2)
C=[]
for j in range(37):
    C.append(sum(fac(k)*comb(j,k) for k in range(min(j,18)+1))
             -sum(fac(k)*fac(j-k) for k in range(max(0,j-18),min(j,18)+1)))
assert C[:4]==[0,0,0,0] and all(a>0 for a in C[4:28])
assert sum(Fraction(max(0,-C[j])*(j-4),36**(j-27)) for j in range(28,37))<23*C[27]
print("G coefficients [4,17]:",C[4:18])

# FKS Cor. 2.9, Table 8. Rounded up.
cs=[('7.8','4.11'),('8.17','3.70'),('8.54','3.62'),('8.93','3.54'),
    ('9.34','3.46'),('9.75','3.38'),('10.18','3.30'),('10.62','3.22'),('11.08','3.14')]
cut=[I(j)/1000 for j in range(780,875)]+[I('.8745'),I('.8749'),I('.87495'),I('.87499'),I('.874999'),I('.875')]
weights=[]
for i,s in enumerate(cut[:-1]):
    a,b=map(I,cs[min(8,max(0,(780+i)//10-79))])
    r=(8*s-5)/3; q=5-2*s
    fall=I(1); facsum=I(1)
    for j in range(1,5):
        fall*=q-(j-1)
        facsum+=fall/(r*h0)**j
    w=a*(-r*h0).exp()*h0**q/r*facsum+b*(h0*h0+2*h0+2)/H
    weights.append(w)
assert all(x.a>y.b for x,y in zip(weights,weights[1:]))
vs=[(1-cut[i],2*(weights[i-1]-weights[i]),0) for i in range(1,len(weights))]
vs += [(I('.125'),2*weights[-1],0),(I('.25'),I('2.091'),1)]
vpoly=[(I('.22'),I('.0071'),2),(I('.5'),I('.0142'),2)]+vs

# These checks are on constants and exact algebra, not sample-curve evidence.
b=I(30); l2=I(2).log()
anchor=(b/l2).log()+sum((b**k-l2**k)/(k*fac(k)) for k in range(1,160))
# Remainder positive, < 2 b^160/(160*160!).
ar=(2*b**160/(160*fac(160))).b
delta=anchor+I(0,ar)-b.exp()/b*factpoly(b)
assert 12 < delta.a and delta.b < 13
print("Li2 anchor minus F18:",delta)
p=I(34); w=2*(p/(pi*I(1).exp())).log()
assert ((w-I('2.4'))*(2*p-w-I('2.4'))+4).a>(8*pi*I('1.007')).b
assert (I('1.000000147')+I('1.78')*(-p/6).exp()).b<D('1.007')
assert (2*pi**2*(I(34)/2).exp()/34).a>10**7
assert (2*pi**2*(I(58)/2).exp()/58).b<H
assert (3*I(12).exp()/I(100).exp()+(c*I('1.2')+351*(-I(50)).exp())/100**2).b<D('2e-16')

# At density scale h=exp(-L/4), L>=100.
assert (1/(64*pi)+I('.933')/100**2+1/(2*pi*100)+2/(pi*100**2)).b<D('.007')
assert (I('2.45')/(2*pi)).b<1
assert ((I(100)/4).exp()-5*I(100)-2).a>0
assert (I(100)/4).exp().a>51
assert (I(100)/4).exp().a>500
assert (I('.0071')-1/(64*pi)-I('.9321')/100**2).a>0

def dense(L,scaled=False):
    u=I('.125') if scaled else I(0)
    return sum(a*L**k*((u-r)*L).exp() for r,a,k in vpoly)
def EC(L):
    return 3*L*(12-L).exp()+c*(1+I('1.2')/L)+117*(-L/2).exp()*(1+3/L)
def EF(L):
    return 3*L*(7-L).exp()+(L*L+2*L)*(-L/2).exp()/(8*pi)
def EF2(L):
    k=(1-I('2.4')/L)**2
    return 3*L*(7-L).exp()+(-L/2).exp()/(8*pi)*((L-I('2.4'))**2+
        2*L*(k+(1-k)*((34-L)/2).exp()))
def ED(L):
    return I('2e-16')*L*(100-L).exp()+sum(
        a*L**k*(-r*L).exp()*(1+1/((I('.98')-r)*L)) if r.b<D('.98')
        else a*(-L).exp()*(1+L/100) for r,a,k in vpoly+[(I('.5'),I(3),0)])
def E(L,d,upper=False):
    ls=[EC(L)]
    if L.a>=7 and L.b<=58: ls+=[EF(L)]
    if L.a>=34 and L.b<=58: ls+=[EF2(L)-(2*(-L/2).exp()*(1+2/L*(1-((34-L)/2).exp())) if upper else 0)]
    if L.a>=100 and d: ls+=[ED(L)]
    return I(0,min(x.b for x in ls))+(13*L*(-L).exp()+3*fac(19)/L**19 if upper else 0)

def los(L,d):
    a,b=E(L,d,True),E(L-1,d)
    return L**4*(L/(L-1)*b+2*factpoly(L)*a+a*a)

def part(n,L):
    return sum(C[j]/L**(j-4) for j in range(4,n+1))
def connection(a,b,lamb,d=False,n=None,k=100):
    # Prove each closed cell by outward interval inequalities; G decreasing.
    # Endpoints here multiples of 1/k, exact terminating decimals.
    aa=D(str(a))*k; bb=D(str(b))*k
    assert aa==int(aa) and bb==int(bb)
    low=D('Infinity')
    for j in range(int(aa),int(bb)):
        L=I((I(j)/k).a,(I(j+1)/k).b)
        Gend=g(L.b)
        tar=I(lamb) if n is None else part(n,I(L.a))
        bound=Gend-los(L,d)-tar
        assert bound.a>0,(a,b,L,bound)
        low=min(low,bound.a)
    print("certified join",a,b,lamb,n,d,"excess>",low)

def onesided(a,b,margin,k=100):
    assert (I(b).exp()).b<=D('1.2e17')
    lo=D('Infinity')
    for j in range(int(D(str(a))*k),int(D(str(b))*k)):
        L=I((I(j)/k).a,(I(j+1)/k).b)
        U=I(16)*L*(-L).exp()+3*fac(19)/L**19
        F=E(L-1,False)
        val=g(L.b)-L**4*(L/(L-1)*F+2*factpoly(L)*U+U*U)-margin
        assert val.a>0,(L,val)
        lo=min(lo,val.a)
    print('certified one-sided join',a,b,margin,lo)

def tail_d(a,n):
    L=I(a); z=L-1
    em=ED(z)+13*z*(-z).exp()+3*fac(19)/z**19
    assert em.b<D('.001')
    assert (L/(L-1)+2*factpoly(L)+em).b<D('3.1')
    assert (I('3.1')*L**(n+1)*em).b<C[n+1]
    assert (a-1)/8>n+3 and 19>n+1 and a>=101
    print("density tail from",a,"through j=",n)

def exact_endpoint():
    from count import primepi
    getcontext().prec=65
    n=38358837682
    e=I(1).exp(); m=int((I(n)/e).a)
    assert (I(n)/e).a>m and (I(n+1)/e).b<m+1
    a,b=primepi(n),primepi(m)
    assert (m,a,b)==(14111427770,1644673232,632207037)
    print('endpoint counts:',n,m,a,b)
    def f(x): return e*b*x/x.log()-a*a
    # Increase resolution independently by sign bisection.
    L,U=I(n).a,I(n+1).b
    for _ in range(40):
        m=(L+U)/2
        y=f(I(m))
        if y.a>0:U=m
        elif y.b<0:L=m
        else:raise ArithmeticError("unresolved sign")
    assert f(I(L)).b<0 and f(I(U)).a>0
    print("endpoint",L,U,"integers",a,b)
    assert f(I(n)).b<0 and f(I(n+1)).a>0
    assert (e*b*(I(n).log()-1)/I(n+1).log()**2).a>67000000


if __name__=="__main__":
    if "--endpoint" in sys.argv: exact_endpoint()
    assert I('36.98').exp().b<D('1.15e16')
    onesided(36.98,37.5,I('.10'))
    onesided(37.5,39.32,I('.32'))
    onesided(39.1,39.32,I('.8'))
    for pars in [(39.32,39.5,'.065',False,None,200),(39.5,40,'.145',False,None,100),(40,42.8,'.35',False,None,100),(42.8,43,'1',False,None,200),
                 (43,60,'1.038',False,None,100),
                 (46,77,'1.209',False,None,25),(47,67,'1.246',False,None,25),
                 (60,163,'1',True,None,10)]:
        connection(*pars)
    for n in [4,5,6,8,10,12,14,16,17]:
        for a in range(max(101,8*(n+3)+2),1200):
            z=I(a-1)
            em=ED(z)+13*z*(-z).exp()+3*fac(19)/z**19
            if (I('3.1')*I(a)**(n+1)*em).b<C[n+1]:
                tail_d(a,n); break
    for L,k in [(100,'.055'),(165,'.025'),(200,'.02'),(300,'.016'),(500,'.014'),(1000,'.013'),(3000,'.012')]:
        if L==100:k='.065'
        assert dense(I(L),True).b<D(k)
        print("density constant",L,k,dense(I(L),True))
