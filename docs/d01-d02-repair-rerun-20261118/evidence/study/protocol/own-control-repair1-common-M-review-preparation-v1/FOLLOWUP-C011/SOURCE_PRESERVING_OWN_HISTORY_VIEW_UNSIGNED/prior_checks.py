"""Supplementary exact numerical obligations for all-ray comparisons."""
from certificate import *
from refine import rp,rt
l=F(170)
for c in (F('.011'),F('.0107')):
    assert I(F('.0039')).lt(c*(1-e(-l*F('.003'))))
assert I(F('.0107')).lt(rt(b0)[-1][0])
a0,a1=F('.0227'),F('.321')
for a,x,y in [(160,a0,a1),(250,F('.0162'),F('.227')),
              (400,F('.0136'),F('.191'))]:
    assert (y*e(-F(a,32))).lt(x)
for d,a in [(F(0),F('1.04e-12')), (F(1,8),F('.0039'))]:
    assert (a1*e(-(F(5,32)-d)*l)).lt(F('.99')*a)
    assert (l*rp(b1,l)*e(d*l)).lt(F('.99')*a)
    assert (2*(4*e(-(F(1,2)-d)*l)+10*e(-(F(2,3)-d)*l))).lt(F('.001')*a)
h=log(2000/(2*PI))
assert (2000*(h*h/(2*PI)+F('1.8642'))).lt(20000)
assert (5*10**6*e(-F(2,5)*61)).lt(1)
for Y,t in ((100,F(1)-F('.593')**2),(H,F(100,H))):
    y=log(Y)
    assert ((y*y+2*y+2)/(12*Y)+F(1,Y)).lt(t)
assert I(F('36.95')).lt(log(F('1.15e16')))
assert finite('36.95','37.2',b0,margin=F(0),step=F('.001')) is None
print('both grids / L=170, simple power ratios and signed-contour numerical inequalities, and DP finite join passed')
