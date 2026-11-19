"""No-QRH experiments with the FKS Table 5 information."""
from D02_cert import F, expi, S, r_u, E, factorial, verify_late
from math import isqrt
from ram import gap, I, approx

def y(t):
    d=max(F('4.969e-15')*expi(-F('.0061')*(t-3000))[1], F('.006')/t**4)
    return d*t**4*(1+F('1.008')/t)+F('1.004')*factorial(9)/t**5+F('8e-16')*t**5*expi(3000-t)[1]
def loss(t):
    return (t/(t-1))**5*y(t-1)+(2*t*S(t)+y(t)/t**4)*y(t)
if __name__=='__main__':
    verify_late()
    print('late-loss diagnostics',[(i,float(loss(F(i)))) for i in [3039,3040,3041,3200,3500,4000,5000]])
    for t,c in [('3039.2','.0005'),(3040,'.004'),(3200,'.50'),(3500,'.89'),(4000,'.98')]:
        # For t>=3041, nonincreasing loss and main >1 give the whole ray.
        # For earlier points, main >1+14/t due to positive remaining
        # terms dominating the negatives, use t<=3041 first.
        if F(t)<3041:
            assert loss(F(t))<1+F(14,3041)-F(c)
            assert loss(F(3041))<1-F(c)
            print('early+late all-ray passed',t,c,flush=True)
        else:
            assert loss(F(t))<1-F(c)
            print('late all-ray passed',t,c,flush=True)
    # CH2 plateau vs unsigned gap scale: at t=1000 this alone
    # supplies endpoint losses >3 in the standard absolute-value transfer.
    assert 3*F('1.048e-12')*1000**4>3
    # Even exp(2000) and exp(2900) considered as *own* table anchors:
    assert 3*2000**4*F('2.4746e-12')>100
    assert 3*2900**4*F('9.2091e-15')>1
    print('plateau and native table anchor loss diagnostics checked')
    x=gap(I(755),None,4)
    assert x.b<0
    print('failure of the CH2 envelope at 755 (not a negative value of R)')
