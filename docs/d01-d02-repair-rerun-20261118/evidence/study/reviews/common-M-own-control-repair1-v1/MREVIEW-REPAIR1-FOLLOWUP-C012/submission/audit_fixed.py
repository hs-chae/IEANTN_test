"""Fixed checks of disclosed obligations, no search for new parameters.
Run with PYTHONPATH pointing to a byte-exact restored candidate."""
from verify import *
from mertens import J
from enhanced import D, pc
x=Q('38358837682.1')
r=ex(1)*x*632207037/ln(x)-1644673232**2
assert (r+7974586).yes() and (-7974585-r).yes()
print('exact interval: -7974586 < R(38358837682.1) < -7974585', r)
print('pointwise sufficient-test diagnostic at L=31',lower(Q(31),Q(31),0,0))
assert lower(Q(31),Q(31),0,0).b<0
pi_min=Q('25.1327412')/8
for u,c in [(14,Q('.1')),(H,Q('1e-11'))]:
    z=2/pi_min*(1+ln(u)-ln(2*pi_min))/u
    assert (c-z).yes()
    print('oscillatory zero mass cap at U=',u,z)
assert (2*ln(2*pi_min)+ln(Q(3,4))).yes()  # elementary signed term positive inside parentheses
assert (I('2.1')-ln(2*Q('3.141594'))).yes()
print('D_4(.77)',D)
print('scaled coarse B1 at 200',shifted(Q(200),M1,Q(5,32)))
c=32*ln(Q('.2612')/Q('.01318'))
assert (c-95).yes() and (96-c).yes()
print('early two-row crossover',c)
for q in [Q('.2'),Q('.3')]:
    assert (q-Q('.01334')*40**2*ex(-5)).yes()
print('old simple B0 power row already beats original Dusart target strengths at and beyond L=40')
d=ln(767135587)
assert (Q('.1973')-Q(1,6)-Q(5,8)/d-Q('1.02')*d*d/(767135587-1)).yes()
print('Dusart directional asymptotic .1973 check at analytic onset passed')
