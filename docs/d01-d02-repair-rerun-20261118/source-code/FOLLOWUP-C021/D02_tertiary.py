"""Exact comparisons for tertiary.md."""
from cert import F,expi
from density import d,A,Q
def ex(x):return expi(x)[1]
def verify():
    for b,t,z,c,cap in [(A,F(200),F('.455'),F('.227'),F('5e-10')),
                        (Q,F(187),F('.0281'),F('.014'),F('7e-8'))]:
        k=1-b
        assert 2/t<k
        assert z*t*t*ex(-k*t)<cap
        assert b*c*ex(-k*t)+(t+1)*ex(-t/2)<F('1e-12')
        assert d(b)[0]>F('.001')
        assert 3000*t*t*ex(-b*t)<F('1e-12')
        assert (2+F('1e-10'))*c<z and z*ex(-k*t)<1
    t=F(200)
    d0=F('.227')*ex(-5*t/32)
    u0=d0+F('1.4262')*ex(-t/2)
    assert (1+u0)*(1+F('.455')*ex(-5*t/32))<1+F('1e-12')
    assert u0+(t+1)*ex(-t)<F('1e-12')
    assert u0<F('.01')
    # theta(x)>=.99x, log theta(x)>=t-.011 for t>=200.
    assert (1+1/t)/(F('.99')*(1-F('.011')/t))<2
    print('Tertiary certificates passed')
if __name__=='__main__':verify()
