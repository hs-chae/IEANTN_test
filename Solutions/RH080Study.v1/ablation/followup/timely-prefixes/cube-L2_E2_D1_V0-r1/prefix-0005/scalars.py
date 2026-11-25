"""Reproducible rational checks for the written arguments; no network or floats."""
from fractions import Fraction as Q
from math import factorial

def exp_bounds(x, n=160):
    x=Q(x)
    assert x>=0 and x<n+2
    low=sum(x**j/factorial(j) for j in range(n+1))
    upper=low+x**(n+1)/factorial(n+1)/(1-x/(n+2))
    return low, upper

pl,pu=Q('3.141592'), Q('3.142')  # Mathlib pi_gt_d6 and the weaker consequence pi<3.142 of pi_lt_d6
m,T,s=Q(2154433),Q('14.58304'),Q('1467.798')
assert s*s<m
assert exp_bounds(14)[1]<m<exp_bounds(T)[0]
assert (m+1)**3<=10**19 and m**3>=2300000000
assert 2/pu>Q('.636') and 2/pl<Q('.637')
assert exp_bounds(Q('2.239'))[1] < 2*pl*Q('.997')*Q(3,2)*m/(m+1)
assert 2*pu*Q('.997')*Q(3,2)<exp_bounds(Q('2.25'))[0]
assert 2*pu*Q(3,2)/m < Q('.00001')
assert Q(997,3) < exp_bounds(Q('5.81'))[0]
assert exp_bounds(Q('.9'))[1]<Q('2.5')
assert exp_bounds(Q('1.7'))[1]<Q('5.5')
assert exp_bounds(2)[0]>7
assert exp_bounds(Q('.6'))[1]<2
assert max(pu-Q('2.5'),Q('3.5')-pl)<=Q('.642')
assert max(2*pu-Q('5.5'),7-2*pl)<Q('.785')
pu_sin=lambda u: u-u**3/6+u**5/120
assert pu_sin(Q('.642'))<Q('.60') and pu_sin(Q('.785'))<Q('.71')
assert (T+2)/s<Q(1,50)
assert 2+1/s+12*Q(1,50)<3
assert Q('1.68')/(50*s)+Q('1.5')/(50*s)+Q(9)/(50*s)+Q('0.000001')<Q('.001')
g=Q('5.81')
k1=Q('.636')*Q('.4')/Q('3.5')
k2=Q('.636')*Q('.29')*Q('1.5')/7
assert Q('.637')*(2+g)-k1-k2<Q('4.864')
assert Q('.637')*(g+g*g/2+Q('.00001')-(2+g)*Q('2.239'))+k1*Q('1.35')+k2*Q('.55')+Q('.001')<Q('3.45')
assert (Q('.997')*(1-1/m)-(Q('4.864')*T+Q('3.45'))/(3*s))*(1-1/(14*m))>Q('.98010')
assert (1-Q('.98010'))**2*1013>Q(19,30)**2
assert exp_bounds(4)[0]/8>Q('6.82')
assert exp_bounds(Q('4.125'))[0]/Q('8.25')>Q('7.49')
assert exp_bounds(6)[0]/12>32
assert exp_bounds(8)[0]>2980>1024
d=Q('.91015')
assert (1+2/Q(2980))*(1+1/Q(8*2980)) < Q('1.001')
assert Q(8,9)-(d-Q('4.2')/Q('24.75'))/Q('6.82')>Q('.7803')
assert Q(8,9)-(d-Q('4.2')/36)/Q('7.49')>Q('.7803')
assert Q(8,9)-(d-Q('4.2')/37)/(8/Q('1.001'))>Q('.7803')
assert Q(8,9)-d/(Q(32,3)/Q('1.001'))>Q('.7803')
print('PASS: exact rational enclosures and final scalar inequalities')
