"""Numerical leaves for the all-ray comparison of the explicit portfolios."""
from applications02 import *
def run_compare():
    B=I(200)
    eps=F('.00666')
    floor=I(eps)*ex(-B/8)
    # New power rays through the strongest own original-input frontier.
    assert low(I(eps/2),I('.265')*ex(-B/32))
    assert low(I(eps),I('.85')*ex(-B/32))
    for c,g,k in [L0[-1],LS[-1],(*layers[-1],0),(*HIG[-1],0)]:
        assert g==GAP0 and low(c,eps)
    assert all(v[-1][1]==GAP0 and low(v[-1][0],eps)
               for (h,a,o,j),v in RM.items() if j==1)
    assert low(PI/(3000175332800-1),floor)
    assert low(PI/H,floor)
    assert low(I('.001')/B**4,floor)
    assert low(I('.09')/B**6,floor/B)
    assert low(I('.09')/B**5,floor)
    # e^{-sqrt(L)}, main relative exponent in the conservative comparison.
    assert low(ex(-power(B,F(1,2))),floor)
    X=I(1000)
    assert low(I('6e-6')*ex(X/8-power(X,F(1,2))),eps)
    u=I(H).log(); p=(2*PI).log()
    assert low((125-u)*((125+u)/2-p)/(2*PI),1)
    assert low(1-ex(-F(2,5)*X),F(1,2))
    # Dusart formula lower term uniform in m, delta at printed H.
    HH=2445999556030
    Q=I(HH).log()
    assert low(I('1e-8'),0) and low(I('51.5')*Q**2/HH,I('1e-8'))
    assert low(I('5.573412')*Q,100)
    assert low(1,HH*I('.01332')*ex(-B/8))
    assert low(I('2.5e-9')*ex(-B/100),floor)
    # Ratio for plain powers: new early row vs best early B0 row.
    assert low(I('.262')*ex(-I(91)/32),I('.015'))
    assert low(I('.015'),I('.262')*ex(-I(92)/32))
    assert low(I('.45')*eps,I('.221')*ex(-B/32))
    assert low(I(eps),I('.71')*ex(-B/32))
    assert low(PI/(2*(3000175332800-1)),floor)
    assert low(I(eps)/10,I('1.000000147')*ex(-(F(1,2)-GAP0)*B)+I('1.78')*ex(-(F(2,3)-GAP0)*B))
    assert low(I('6.78e-29'),I(eps)*ex(-X/8))
    assert low(I('.32')/B**3,floor)
    assert low(I('.01277')*ex(B/32)/I('.221'),29)
    assert low(I('.041')*ex(I(201)/32)/I('.71'),30)
    print('comparison guards passed; all-ray derivatives in comparison.md',flush=True)
if __name__=='__main__':run_compare()
