from pathlib import Path
import sys
sys.path.insert(0,str(Path.cwd()))
from ram_repair import Q, c, q, el, eu, pl, pu, logb, wt_refined, psi_new, theta_new
from d02_mcheck import g_tests,m_anchor
from d01_cert import exp_bounds,ln_bounds
g_tests();m_anchor()
A=Q(200)
assert 51<A<64*el(A/8) and 64*eu(A/8)<(el(A/2)-2)/5
cap=Q(".15916")*Q(".142")**2+Q("3.7284")/A**2+Q("2.091")/(64*A)+118*eu(Q(-75))/A**2
assert cap<Q(".004")<Q(1,64)
print("density-free normalized bound", float(cap))
assert el(Q(40,3))>51 and el(Q(20))>5*eu(Q(40,3))+2
assert el(Q(93))>570 and el(Q(2))>5+2*eu(Q(-95))
assert el(Q(191))>eu(Q(190))
# Ancillary repair of the stated anchor justification, not of a numerical target:
a=Q(40)
pt=Q("1.95")+Q("3.9")/a+Q("19.5")/a**2+2*a*eu(-a/2)
assert pt+c*a**2<128
print("u=40 pi/theta anchor, sqrt-unit bound",float(pt+c*a**2))
assert Q(".0463")*(1+2*Q(192,190*191)/Q(3*10**12))>0
assert Q("4.49e-15")*(1+2*Q(192,190*191)/Q(3*10**12))<Q("4.5e-15")
assert el(Q(28))>10**11 and eu(Q("27.75"))<Q("1.15e16")
assert eu(Q("29.9"))<10**13 and eu(Q("43.7"))<10**19
assert eu(Q(58))<Q("2.169e25")
assert el(Q("36.98"))>10**11 and eu(Q("36.98"))<Q("1.15e16")
assert 10**11>38358837683
n=38358837682
x=n+Q(1,5)
l,h=ln_bounds(x)
a,b=exp_bounds(1)
lo=a*632207037*x/h-1644673232**2
hi=b*632207037*x/l-1644673232**2
assert -1220000<lo<hi<-1200000
print("Counterexample enclosed (-1220000,-1200000)")
assert wt_refined()[-1]==(Q(".87499"),Q(".01045365"))
assert wt_refined(True)[-1][0]==Q(".8749999")
assert psi_new(Q(185))<Q(".01973")
print("density terminal bounds",wt_refined()[-1],wt_refined(True)[-1])
for L,k,top in [(18,0,100000000),(19,0,1500000000),("19.5",0,2500000000),(21,0,10000000000),(23,0,10000000000)]:
 assert eu(Q(L))<top
assert Q("1.5")*Q(".19998")==Q(".29997")<Q(".29998")

