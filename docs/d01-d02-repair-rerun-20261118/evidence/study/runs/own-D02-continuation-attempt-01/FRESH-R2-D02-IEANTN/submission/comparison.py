#!/usr/bin/python3.10
"""Elementary endpoint comparisons with the published-source Mertens control."""
from d02 import *
V=3000175332800
# Uniform floor for centered CH2 bounds and their direct weighted transfers.
assert (piB/V*(1-piB/(3*10**7))).above('1.04e-12')
assert (19*exp0(F(169,2))/169).above(V)
assert (I('.01')/169**4).above('1.04e-12')
assert (I('.01')/169**4).above(I('.005')*exp0(-F(169,8)))
assert (3*exp0(-F(169,2))).below('1e-17')
assert (3*exp0(-F(3*169,8))).below('.001')
assert (I('.004')*180**2*exp0(-F(180,8))).below('3.781e-8')
for a,c in [(200,'1.017e-8'),(201,'1e-8'),(220,'1e-9'),(230,'3e-10')]:
 assert (I('.004')*a*a*exp0(-F(a,8))).below(c)
# Dusart's printed Table 1 cut: up through 1000 vs the later rows.
assert (I('.005')*exp0(-F(1500,8))).below('2.35e-20')
# PT printed Table 1 constants start at L=1000, too large to narrow the control.
assert (I('.005')*exp0(-125)).below('6e-29')
# FKS arbitrary leading R in Thm 1.2 must cover at least one verified ordinate
# in (18,1000]; PT Lemma 2 proves such an ordinate exists by subtraction.
assert exp0(1).above(2)
assert (2*piB*exp0(1)).below(18)
def zl(t):return log(I(t)/(2*piB))**2/(4*piB)
assert (zl(1000)-zl(18)).above('1.8642')
assert (2/log(1000)).above('.28')
assert 4*1000 < F('.28')*120**2
assert 1000**3 > F('5.574')**3*1000**2
assert (I('6e-6')*1000*exp0(5)).above('.005')
assert (I(1000**2)/H).above('1e-12')
assert (log(2)*log(I(H)/(2*piB))/(2*piB)).above(1)
assert (1-exp0(-400)).above('.5')
# FKS 1.4 / 5.2 on their stated domains: 0.848 sqrt(t) < t/8 for t>=169.
assert F('.848')**2*169 < F(169,8)**2
print('Published-source model comparison endpoint inequalities verified.')

a=F(200);b=B2;alpha=1-b
C=I('.015626')
assert (I(1)/64+(I('1.000000147')*exp0(-(b-F(1,2))*a)+I('1.78')*exp0(-(b-F(1,3))*a))/(a*a)).below(C)
t=F(220)
scaleV=C*(1+I(1)/b/t)+(v2(a)+C*a*a*exp0(-alpha*a))*exp0(a-b*t)/(a*t)
assert scaleV.below('.0158')
assert (I('.0158')*(exp0(alpha)+I('2.02')+I('.0158')*221**2*exp0(-alpha*221))).below('.051')
base=(1+I(1)/alpha+2/(I(alpha)**2*a)+2/(I(alpha)**3*a*a))/64
other=(1+I(1)/alpha+(I(1)/alpha+I(1)/I(alpha)**2)/a)/64
assert (base+pp(a,b)/(a*a)).below('.123')
other+=pp(a,b)/(a*a)
assert (other/(1-other*a*exp0(-alpha*a))).below('.123')
print('Direct-premise fallback comparisons verified.')
