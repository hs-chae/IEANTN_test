"""Rational certificates for the Mertens, cancellation, tertiary claims."""
from cert import F, rounded_weights

from cert import exp_bounds, ln_bounds, ehi, bracket, power_coeff, rup

D=F('1.048e-12'); P=F('.01955')
b=F('1.000000147');c=F('1.78');H=3*10**12
def high_cut(s,z):
    r=(8*s-5)/3
    assert z>4/r
    a,b=bracket(s)
    return 2*(a*ehi(-r*z)*z**4/(r-4/z)+b*ehi(-z)*z**2/(1-2/z))

def tails(L,w):
    assert L>=190
    z=L/2-2
    bands=list(map(F,['.70','.75','.80','.85','.875']))
    E=(L/2)**2/6+2
    return (10*E*ehi(-F('.175')*L) + 2*power_coeff(L,w)/H
        + F('8.364')*L**2*ehi(2-3*L/8)
        + sum(high_cut(s,z)*ehi((t-F('.875'))*L)/(1-t)
              for s,t in zip(bands,bands[1:]))
        + 8*P*ehi(-L/4)+F('2.01')*ehi(-3*L/8))

def cert_analytic():
    w=rounded_weights()
    for L,k,a in [(F(190),F('8e-9'),F('.01955')),
                  (F(400),F('9.1e-15'),F('.01361'))]:
        K=tails(L,w)
        C=power_coeff(L,w)+b*ehi(-3*L/8)+c*ehi(-F(13,24)*L)
        lz=C+(1+1/L)*K+L*ehi(-7*L/8)
        tiny=ehi(-L/8)/L
        assert lz*tiny<1
        assert K<k and C+K<a and lz/(1-lz*tiny)<a
        print("L, upper integrated-error coefficient",int(L),float(K))
        # primorial recentering followed by exp
        v=(1+1/L)*K+2*P**2*ehi(-L/8)+L*ehi(-7*L/8)
        if L==400: assert v/(1-v*tiny)< F('9.2e-15')

    assert 2*b-F('.9999')+F('1.5')*c*ehi(-F(40,6))<F('1.004')
    # Moderate ray constants in mertens.md; upper loss at L=40 from CH2.
    L=F(40); X=F('114.674')
    mb=(2*D+X*(1+2/L)*ehi(-L/2))/L
    wb=D+X*ehi(-L/2)
    assert mb+F('2.2')*ehi(-L/2)/L+2*ehi(-L)<F('7e-9')
    assert wb+F('2.2')*ehi(-L/2)+2*L*ehi(-L)<F('3e-7')
    # Full scaled loss through [21,40], terms use monotonicity or fixed max at 40.
    L=F(21)
    assert F('6.6')*L**2*ehi(-L/2)+5*L**3*ehi(-L)+F('7e-9')*40**3 < F('.082')
    assert F('6.6')*L**2*ehi(-L/2)+4*L**3*ehi(-L)+F('3e-7')*40**2 < F('.082')
    # [40,190]: exp-terms decreasing once L>=40, constant terms maximized at 190.
    L=F(40)
    assert 2*D*190**2+X*(L**2+2*L)*ehi(-L/2)+L**3*ehi(-L)<F('.0005')
    assert D*190**2+X*L**2*ehi(-L/2)<F('.0005')
    # [190,infty): scaled pure powers decreasing; compare baseline coefficients.
    L=F(190)
    assert P*L**2*ehi(-L/8)<F('.0005')
    L=F(25)
    assert F('6.6')*L**2*ehi(-L/2)+5*L**3*ehi(-L)+F('7e-9')*40**3<F('.016')
    assert F('6.6')*L**2*ehi(-L/2)+4*L**3*ehi(-L)+F('3e-7')*40**2<F('.016')
    assert exp_bounds(21)[1]<1318815735
    assert exp_bounds(25)[1]<72004899338
    l,u=ln_bounds(10**7)
    assert 16<l<u<F('16.2')
    assert F('2.8e-9') < (1/F('16.2')-F(1,16**2)-F('.001')*(3+F(1,16))/16)/(2*10**7)
    assert F('3.1e-9') > (F(1,16)-1/F('16.2')**2+F(2,16**3)+F('.001')*(3+F(1,16))/16)/(2*10**7)+F(1,2*10**14)
    assert (F('.04')-2*P)-P*F(7,8)*F('.04')*ehi(-F(190,8))>F('.0008')
    assert F('.04')*ehi(-F(190,8))<F('.001')
    assert 2*P*ehi(-F(400,8))<F('.01')

if __name__=='__main__':cert_analytic()
