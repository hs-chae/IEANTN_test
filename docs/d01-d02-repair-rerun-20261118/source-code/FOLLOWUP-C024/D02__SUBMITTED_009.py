"""Rational verification of analytic Mertens comparisons."""
from cert import F, lni, expi, a, W, W1, W2

k=F(5,32)
b=F('29.9')
c=F(57)
D=F('.791')
Dm=F('.751')
Bh=F('113.67')

def ex(x):return expi(x)[1]
def V(t):
    return F('1.05')*ex(-t/2)+F('.75')*ex(-2*t/3)+10*ex(-3*t/4)
def h(t):return a+Bh*ex(-t/2)

def verify():
    assert c<lni(F('2.169e25'))[0]
    assert b<lni(F('1e13'))[0]
    assert expi(F(220))[0]>224 # used only to certify exponents elsewhere
    assert F('3.965')/(lni(F(2))[0]*28/3)**2 < F('.1')
    # theta(v)/v in [.97,1.01] for v>=10^4.
    assert F('.791')/100 < F('.01') and (F('.791')+F('1.4262'))/100 < F('.03')
    assert a+(Bh+F('1.4262'))/3_000_000 < F('.01')
    U=h(c)+F('.04')*c*c*ex(-c/2)
    J=(h(c)+U)/c
    H0=U+F('.08')*(b*b+4*b+8)*ex(-b/2)
    K0=J+F('.08')*(b+3)*ex(-b/2)
    # All terms in the decaying parts of t^2(H+V), t^3(K+V/t)
    # decrease for t>=19.4. The remaining constants times powers increase.
    def mesh(l,r,step,fn):
        while l<r:
            u=min(l+step,r)
            assert max(fn(l,u))<F('.0899'),(l,u,[float(v) for v in fn(l,u)])
            l=u
    def low(l,u):
        return (((D+2*Dm)*ex(-l/2)+V(l))*l*l+H0*u*u,
                ((D+2*Dm*(1+1/l))*ex(-l/2)+V(l))*l*l+K0*u**3,
                (Dm+2*D)*ex(-l/2)*l*l+H0*u*u,
                (Dm+2*D*(1+1/l))*ex(-l/2)*l*l+K0*u**3)
    def mid(l,u):
        return ((F('.04')*(3*l*l+8*l+16)*ex(-l/2)+V(l))*l*l+U*u*u,
                F('.04')*(3*l+6)*ex(-l/2)*l**3+V(l)*l*l+J*u**3)
    assert F('19.4')<28*lni(F(2))[0]
    mesh(F('19.4'),b,F(1,8),low)
    mesh(b,F(50),F(1,4),mid)
    assert 2100**2*a+50**2*(Bh*ex(F(-25))+V(F(50))) < F('.0899')
    assert 2100**2*2*a+50**2*(Bh*ex(F(-25))*(1+F(2,50))+V(F(50))) < F('.0899')
    # FKS Cor. 1.4 implies d(s)<=250/s^4 for s>=2100.
    from math import isqrt
    q=1<<44
    L=F(isqrt(2100*q*q),q)
    assert L>11/F('.8476836')
    assert F('9.22022')*2100**5*(L+F(1,q))*ex(-F('.8476836')*L)<250
    t=F(2100)
    assert 250*(1/(3*t)+1/t**2)+t*t*V(t) < F('.0899')
    assert 250*(1/(4*t)+F(6,5)/t**2)+t*t*V(t)< F('.0899')
    # Converts .099 scaled log error to .1 scaled relative error.
    assert F('.0899')*F('.09')/F('19.4')**3<F('.0001')
    # Closed form hypothesis-based bound dominates 0.2/t^3 above t=200.
    t=F(200)
    f=ex(-k*t)/64*(t+(t+1)/k+1/k**2)+V(t)/t
    u=ex(-k*t)/64*((1+1/k)*t*t+2*t/k**2+2/k**3)+V(t)
    assert f*t**3<F('.001') and u*t**2<F('.001')
    assert 5/k<t
    # Source-based QRH power tails.
    t=F(258)
    dq=W(t)*ex(-t/8)+F('117.5')*ex(-t/2)
    iq=(8*W(t)+64*W1(t)+512*W2)*ex(-t/8)+235*ex(-t/2)
    assert (dq+iq+V(t))*t*t<F('.000999')
    assert (dq+(1+1/t)*iq+V(t))*t*t<F('.000999')
    assert 4/t+F(1,40)<F(1,8)
    # Tail estimates used in finite sieve for M and B3.
    assert F('.791')+F('1.4262')<F('.00014')*16384
    assert a+(Bh+F('1.4262'))/3_000_000 <F('.00014')
    print('Analytic Mertens certificates passed')

if __name__=='__main__':verify()
