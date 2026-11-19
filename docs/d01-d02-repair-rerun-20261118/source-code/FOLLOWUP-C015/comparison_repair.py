"""Exact crossing guards for the repaired envelopes."""
from analytic import *
def ratio(x,k,c,d):
    L=I(x)
    return I(c)/I(d)*L**k*ex(-L/8)
for x,k,d in [
    ('15.7',2,'.185'),('15.7',2,'.19'),('15.89',2,'.175'),
    (16,2,'.160'),(16,2,'.167'),('17.6',2,'.09'),('17.7',2,'.09'),
    (22,3,'.5'),(34,4,'4'),(56,5,'.3')]:
    assert F(x)<200 and 8*k<200
    assert low(ratio(x,k,'.0199',d),1) and low(1,ratio(200,k,'.0199',d))
    print('one crossing after',x,'and before 200 for .0199 versus',d,k)
assert 193>8*5 and low(1,ratio(193,5,'.0196','.3'))
assert low(I(10**12+3),ex(I('27.6')))
assert low(I(11_500_000_000_000_000),ex(I('36.526')))
print('later power dominance, normalized CH2 trigger and analytic sign join: PASS')
