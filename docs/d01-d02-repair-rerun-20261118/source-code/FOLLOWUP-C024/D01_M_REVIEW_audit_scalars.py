"""Review-only source/parameter and endpoint arithmetic; no new parameter search.
Usage: /usr/bin/python3.10 /work/submission/audit_scalars.py /work/exact
"""
import sys
from pathlib import Path
from math import factorial
r = Path(sys.argv[1])
sys.path.insert(0,str(r))
from D01_check import I,F,log,exp,less,approx,PI,TS,AT,BT,rng,fac,LN2
from D02_cert import expi,lni
from power import c,Q,J,mass
from ram import rr, losses, lower, gap, P, C, dd
from mertens_new import add

# Independent join checks on the locked proof's existing constants.
for T,a,b in zip(TS,AT,BT):
    assert 10**7<=T<=3000175332800
    less(PI/(T-1)+PI**2/(3*T*T),a)
    orig=(log(T/(2*PI))**2-log(T/(2*PI))/3)/(2*PI)
    less(orig,b)
    less(2,b)
less(BT[-1]+I('1.4262'),'115.1')
less(I('113.67')+I('1.4262'),'115.1')
less(PI/(3*10**12),'1.048e-12')
less(1/(8*PI),'.04')
less(exp(I(57)),'2.169e25')
less(exp(I('43.749')),10**19)
less(exp(I('36.88')),exp(I(58)))
less(log(38358837683),'36.88')
less(log(100),exp(I(80)/3))
less(51,exp(I(80)/3))
less(2*PI*exp(I(1)),I('2.45')*exp(I(80)/3))
# FKS Table 5: separate epsilon_2, epsilon_3, epsilon_4 columns, rounded
# up independently by one unit of the respective last printed place.
assert F('1.5875e-128')+F('1.4555e-16')+F('4.8224e-15')<F('4.968e-15')
assert F('8.3088e-172')+F('2.5204e-19')+F('1.0770e-17')<F('1.103e-17')
less(5*exp(I(67))/I('2.45')+2,exp(I(1500)))
less(4000,exp(I(67))/I('2.45'))
less(I('2.091')*I('2.45')*4000*exp(I(-67)), '1.7e-25')
# Positive gaps and an exact rational counterexample to the quoted real
# interval (using the independently replayed counts on [n,n+1]).
n=38358837682
P0=1644673232
Q0=632207037
for s in ['.1','.217926','.217927']:
    x=F(n)+F(s); a=exp(I(1))*I(x)/log(x)*Q0-P0**2
    less(0,a) if s=='.217927' else less(a,0)
    print('real point',str(x),'signed R',approx(a))
# The method-failure diagnostic using both endpoints of the actual minima
# (at a point where the pi sign option is not available).
t=I(755)
def mn(values): return I(min(v.a for v in values), min(v.b for v in values))
u=mn([rr(t,i,True) for i in range(len(TS))])
v=mn([rr(t-1,i,False) for i in range(len(TS))])
less(lower(t)-losses(t,u,v),0)
# Tail/main identities: early late proof uses degree-8 factorial truncation.
from D02_cert import A
assert A[4:8]==[1,14,145,1412]
assert -A[-2]/F(40)**9-A[-1]/F(40)**10<1
assert dd[4:14]==[1,14,145,1412,13985,145450,1610021,19063832,241691425,3277187246]
# Mathematical denominators for both conversions remain positive.
kap=F(5,32); t=F(200)
V=F('1.05')*expi(-t/2)[1]+F('.75')*expi(-2*t/3)[1]+10*expi(-3*t/4)[1]
K=expi(-kap*t)[1]/64*(t+(t+1)/kap+1/kap**2)+V/t
assert 0<K<1 and t**3*K/(1-K)<F('.001')
# Verify the optional regime comparisons in their exact real coordinates.
cross=32*log(I('.262')/I('.01325'))
less(95,cross); less(cross,96)
assert F(1,1)/F('.0045')/64>F('3.47')
# Check small-log recurrence tail allowances used across the running sums.
assert 2*2**60*F(1,3)**41/(41*(1-F(1,9)))<1
assert 2*2**64*F(1,512)**7/(7*(1-F(1,512)**2))<1
assert F(2**64,4*65536**3*(65536-1))<1
assert F(2**64,7*1024**6*(1024-1))<1
# The historical exploratory refined switch checks +3 before adding the
# old B=115.1 theta budget; verify the conservative +4 guard at precisely
# the existing switch as an ancillary check, not a new parameter search.
from D02_cert import WA, WA1, A0
v=F('205.6')
assert WA(v)*expi(-kap*v)[1]+4*expi(-v/2)[1]<F('1.048e-12')
assert F('117.5')+F('1.4262')-F('115.1')<4
assert WA(v)/50>WA1(v) and WA1(v)/50>2*A0
print('older optional refined switch: conservative +4 guard checked')
print('source constants, domains, true-minimum diagnostic and endpoint checks passed')
