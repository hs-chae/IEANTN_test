"""Exact rational certificates; run /usr/bin/python3.10 cert.py."""
from fractions import Fraction as F
from math import factorial, comb
from functools import lru_cache

@lru_cache(None)
def pos_small_exp(x):
    assert 0<=x<=1
    p=s=F(1)
    for i in range(1,29):
        p=p*x/i
        s+=p
    return s,s+2*p*x/29

@lru_cache(None)
def expi(x):
    x=F(x)
    if x<0:
        l,h=expi(-x)
        return 1/h,1/l
    k=1
    while x>k:k*=2
    l,h=pos_small_exp(x/k)
    # Round on each squaring to keep sizes bounded; relative rounding.
    while k>1:
        l,h=l*l,h*h
        q=1<<max(0,(l.numerator.bit_length()-l.denominator.bit_length()-120))
        r=(1<<120) if q==1 else F(1,q)
        l,h=F(l*r//1)/r,F(h*r//1+1)/r
        k//=2
    return l,h

def atom(z):
    z=F(z);p=z;s=F(0)
    for j in range(45):
        s+=2*p/(2*j+1)
        p*=z*z
    return s,s+2*p/(91*(1-z*z))

@lru_cache(None)
def lni(x):
    x=F(x)
    if x<1:
        a,b=lni(1/x)
        return -b,-a
    j=x.numerator.bit_length()-x.denominator.bit_length()
    if x<2**j:j-=1
    a,b=atom((x-2**j)/(x+2**j))
    c,d=atom(F(1,3))
    return a+j*c,b+j*d

a=F('1.048e-12')
B=F('115.1')
lam=F(7,48)
def S(t):
    return sum(F(factorial(j))/t**(j+1) for j in range(9))
A=[sum(factorial(j)*comb(k-2,j) for j in range(min(8,k-2)+1))
       -sum(factorial(j)*factorial(k-2-j) for j in range(9) if 0<=k-2-j<=8)
   for k in range(2,19)]
assert A[:6]==[0,0,0,0,1,14]
def Plo(l,h):
    return sum(F(c)/(h if c>0 else l)**(k-6) for k,c in enumerate(A,2) if c)

# r_u represents t**m*r(t) on a finite interval.
# Point monotonicity of the powers/exponentials bounds the separate terms,
# e.g. t**(m-1)*exp(-t/2) decreases once t>=2(m-1).
def r_u(l,h,m,cond=True,plat=a,anchor=20,J=2):
    assert l>=max(2*(m-1),m) and m<=10
    y={'qrh':F(258),'refined':F('205.6'),'densityA':F(169),'densityQ':F(187)}.get(cond,F(220))
    rate={'qrh':F(1,10),'refined':F(109,800),'densityA':F(5,32),'densityQ':F(1,8)}.get(cond,lam)
    Buse=F(119) if cond=='qrh' else B
    if cond:
        z=min(max(y,l),h)
        assert (m-1)/max(y,l)<rate
        pl=z**(m-1)*expi(-rate*max(z-y,0))[1]
    else:
        pl=h**(m-1)
    return (Buse*l**(m-1)*expi(-l/2)[1]*(1+F(5,2)/l)
            +plat*pl*(1+F(4,3)/l)
            +2*factorial(9)/l**(10-m)+J*l**m*expi(F(anchor)-l)[1])

def E(l,h,m,cond=True):
    # t^(m-1) times loss in t^6 R, using exponent m=5 or 6 (m-5).
    return (l/(l-1))**m*r_u(l-1,h-1,m,cond)+(2*l*S(l)+r_u(l,h,1,cond))*r_u(l,h,m,cond)

def poly_scaled(l,h,m):
    # Lower bound for t**(m-5) times the Taylor lower polynomial,
    # after subtracting the specified prefix in verify_refined.
    return sum(F(v)/(h if v>0 else l)**(k-m-1)
                     for k,v in enumerate(A,2) if k>m)

def verify_mesh(l,h,step,cond,c):
    while l<h:
        u=min(l+step,h)
        if c is None:
            assert Plo(l,u)-E(l,u,5,cond)>0,(l,u,'pos')
        else:
            # t*(P-1) >=14+144/t for t>=40.
            assert sum(F(v)/(u if v>0 else l)**(k-7) for k,v in enumerate(A,2) if k>=7)-E(l,u,6,cond)>c,(l,u,'margin')
        l=u

def verify_ramanujan():
    assert A[6]==145
    assert -A[-2]/F(40)**9-A[-1]/F(40)**10<1
    assert F(1,64)*220**2*expi(-F(5,32)*220)[1]<a
    assert F(5,32)-F(2,220)>lam
    verify_mesh(F('48.25'),F(250),F(1,4),True,F(13))
    # Each term in E(t,t,6) decreases from 250 onwards, including the
    # prefactors t/(t-1), t*S(t), and t*r(t).
    assert E(F(250),F(250),6)<1
    verify_mesh(F(43),F('753.8'),F(1,2),False,None)
    print('Ramanujan analytic certificates passed')

def verify_root():
    from count import N,pi
    el,eh=expi(F(1))
    m=N//eh
    assert (N+1)//el==m==14111427770
    assert pi(N)==pi(N+1)==1644673232 and pi(m)==632207037
    def bounds(x):
        l,h=lni(x)
        return el*x*pi(m)/h-pi(N)**2, eh*x*pi(m)/l-pi(N)**2
    l,h=F('38358837682.217926'),F('38358837682.217927')
    # precise bracket computed separately below if this provisional one fails
    print('root signs',float(bounds(l)[1]),float(bounds(h)[0]))
    assert bounds(l)[1]<0<bounds(h)[0]
    print('Ramanujan last real root certified',l,h)

def W(t):
    return ((t/8+F('2.94'))**2-F('26.88')**2)/F('6.28')+F('3.7284')+F('2.091')*t/48

def W1(t):
    return (t/8+F('2.94'))/(4*F('6.28'))+F('2.091')/48

W2=1/(32*F('6.28'))

def verify_qrh():
    # Elementary enclosing bounds for pi = 4*(atan(1/2)+atan(1/3)).
    def atan(x,n):
        return sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
    q=4*(atan(F(1,2),20)+atan(F(1,3),20))
    assert F('3.14')<q<q+F(1,10**10)<F(22,7)
    assert lni(F('2.45')*48/F('6.28'))[1]<F('2.94')
    assert lni(F('3e12')/(2*F(22,7)))[0]>F('26.88')
    assert lni(F('3e12')/F('6.28'))[1]<F('26.9')
    assert F('26.9')**2/F('6.28')+F('1.8642')<F('117.5')
    t=F(258)
    assert W(t)*expi(-t/8)[1]<a
    assert (W(t)/40-W1(t))>0 and W1(t)/40>W2
    assert (t/8+F('2.94'))>F('26.88')
    # FKS Thm 3.2 height inequalities at 258, then by growth-rate comparison.
    assert 48*expi(t/8)[0]>t
    assert 5*48*expi(t/8)[1]+2<expi(t/2)[0]
    verify_mesh(F('48.25'),F(300),F(1,8),'qrh',F('10.9'))
    assert E(F(300),F(300),6,'qrh')<3
    print('QRH analytic certificates passed')

kap=F(5,32)
A0=kap**2/F('6.28318')
A1=2*kap*F('2.7471')/F('6.28318')+F('2.091')/40
A2=(F('2.7471')**2-F('26.8917')**2)/F('6.28318')+F('3.7284')
def WA(t):return A0*t*t+A1*t+A2
def WA1(t):return 2*A0*t+A1

def verify_refined():
    def atan(x,n):return sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
    pl=4*(atan(F(1,2),20)+atan(F(1,3),20))
    ph=pl+F(1,10**10)
    assert 2*pl>F('6.28318')
    assert lni(98/(2*pl))[1]<F('2.7471')
    assert lni(F('3e12')/(2*ph))[0]>F('26.8917')
    t=F(200)
    assert 40*expi(kap*t)[0]>t
    assert 5*40*expi(kap*t)[1]+2<expi(t/2)[0]
    assert 98*expi(kap*t)[0]>F('3e12')
    # .00000004*t^2 slack more than covers the low zeros.
    coef=1/F('252.1')
    slack=F('0.00000004')
    assert A0-A1*A1/(4*A2)<coef-slack and A2<0
    assert F('117.5')*expi((kap-F(1,2))*t)[1]<slack*t*t
    # Intermediate domain: either Lemma 9.2 or Cor. 1.3 of CH2.
    u=lni(600)[0]
    assert F('1.415')*expi((kap-F(1,2))*u)[1]<coef*u*u
    u=lni(F('1e13'))[0]
    assert a*expi(kap*t)[1]/t**2+F('113.67')*expi((kap-F(1,2))*u)[1]/u**2<coef
    q=F('205.6')
    assert WA(q)*expi(-kap*q)[1]+3*expi(-q/2)[1]<a
    assert WA(q)/50>WA1(q) and WA1(q)/50>2*A0
    verify_mesh(F('48.5'),F(240),F(1,8),'refined',F('13.5'))
    assert E(F(240),F(240),6,'refined')<F('.5')
    # Higher margin on subrays, including the first asymptotic coefficients.
    for left,right,m,target in [(215,300,6,14),(239,325,7,144)]:
        l=F(left)
        while l<right:
            h=l+F(1,4)
            if m==6:
                P=poly_scaled(l,h,6)
            else:
                P=poly_scaled(l,h,7)
                # Powers are t^{-(k-8)} after subtracting 1+14/t.
            assert P-E(l,h,m,'refined')>target,(l,h,'high margin')
            l=h
        assert E(F(right),F(right),m,'refined')<F('.5')
        # Beyond right, the 14 result compares losses with 144/t, also
        # certified by the m=7 endpoint bound.
        assert E(F(right),F(right),7,'refined')<F('.5')
    print('Refined contract analytic certificates passed')

def verify_late():
    R=F('5.5666305')
    Targ=F(67)
    assert (Targ/3)**2 < 3000/R
    assert F('2.091')*F('2.45')*4000*expi(-Targ)[1] < F('1.7e-25')
    assert F('1.103e-17') < F('4.968e-15')*expi(-F('6.1'))[0]
    assert (F('4.969e-15')-F('4.968e-15'))*expi(-F('6.1'))[0] > F('1.71e-25')
    assert F('1.4262')*expi(F(-1500))[1]< F('1e-27')
    # Rational upper evaluation of FKS asymptotic envelope times t^4 at 4000.
    from math import isqrt
    q=1<<44
    y=4000/R
    c=F(isqrt((y*q*q)//1),q)
    assert F('215.823')*y*(c+F(1,q))*expi(-2*c)[1]*4000**4 < F('.0056')
    assert F('5.5')**2*R<4000
    assert F('1.4262')*4000**4*expi(F(-2000))[1]<F('.0004')
    assert r_u(F(3000),F(3000),0,False)+a/3000+B*expi(F(-1500))[1]/3000<F('8e-16')
    def y(t):
        d=max(F('4.969e-15')*expi(-F('.0061')*(t-3000))[1], F('.006')/t**4)
        return d*t**4*(1+F('1.008')/t)+F('1.004')*factorial(9)/t**5+F('8e-16')*t**5*expi(3000-t)[1]
    for v,g in [('3041','.001'),('3060','.08'),('3100','.23')]:
        t=F(v)
        assert (t/(t-1))**5*y(t-1)+(2*t*S(t)+y(t)/t**4)*y(t)<1-F(g)
    print('Unconditional late Ramanujan certificates passed')

if __name__=='__main__':
    verify_ramanujan()
    verify_qrh()
    verify_refined()
    verify_late()
    verify_root()
