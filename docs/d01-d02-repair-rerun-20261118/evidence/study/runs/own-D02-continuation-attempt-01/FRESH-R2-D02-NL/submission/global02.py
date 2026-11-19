
from gap02 import *
from osc02 import pars
from certify import H

def poweru(u,c):
    return sum(b*E((e-c)*u)*(1+1/(u*(1-e-F(1,10)))) for b,m,e,z in P)
def erro(u,c):
    return (sum(b*E((e-c)*u)/u*(1+1/(1-e-F(1,10))) for b,e in [(LOW,F(1,2)),(HIGH,c)])
      +E((1-c)*u)*(G*(1/u+u/20)+400003*u))
assert 1+F(1,175-20)+basic(F(175),20)[1]<F('1.01')
for b,qq,rr in [(B0,F('.015'),F('.048')),(B2,F('.270'),F('.87'))]:
    c=1-b
    assert max(pars(F(175),b))+poweru(F(175),c)+erro(F(175),c)<qq
    assert qq*(F(176,175)/EL(c)+F('2.02'))+qq*qq*E(176*c)<rr
    assert F('.006')*E(F(180,8))<F('1.048e-12')
assert F('.87')*E(F(176,32))<F('.048')
assert F('.270')*E(F(175,32))<F('.005')

for b,a,m in [(B2,32,40),(B2,30,75),(B2,29,145),(B2,28,570),
              (B0,42,55),(B0,40,70),(B0,39,120)]:
    c=1-b;X=a*m
    base=a*E(a*c-1)
    ar=a*E(a-3)
    assert base<1 and ar*F(m+1,m)<1
    assert F(30)*F(2,a)**9+F(28)*a**4*base**m+F(70)*a**5*m*ar**m/EL(29)<1
    assert F(2)*F(2,a)**(m+13)+F(5)*X*E(X-2*m-28)+E(c*X)<1
    print('VARIABLE PASS',b,a,m,X)
# Constants for the certified floor of B0 bounding formulas.
for Q in [Q for j,Q in opts(B0)]+[discrete(B0,s,h) for s in (F('.75'),F('.80')) for h in (F(1,400),F(1,1000))]:
    assert sum(b for b,m,e,N in Q if e==F(1,8))>F('.006')
assert sum(b*E((e-F(1,8))*175) for b,m,e,N in P)<F('.001')
assert F('.005')*E(F(180,8))<F('1.048e-12')
# Smallest comparison envelopes among Dusart 3.3 and 4.2;
# monotonic after 175 because all degree <=4.
for k,B in enumerate(map(F,('0.77','.001','.01','.5','59.18'))):
    assert B/175**k>F('.006')*E(F(175,8))
assert F('.2')/175**2>F('.005')*E(F(175,8))
print('MODEL, JOINS AND COMPARISON CHECKS PASS')

m=125
assert 2/EL(F(1,25))<3
assert 2*(1+F(1,32*m-1))**(m+5)<3
r=1/(32*EL(3))
assert r*F(m+6,m+5)<1
assert E(26)*F(m+2,m+1)<1
assert 7/EL(6)*(m+5)*F(1,32**4)*r**m+800*(m+1)/EL(11)*E(26*m)<F('.005')
assert F('3.125')/(3000175332800-1)>F('.006')*E(F(180,8))
