"""Exact scalar comparisons in candidate.md and Trapezoid.md."""
from fractions import Fraction as Q
from math import factorial

def series(x,n):
    return sum(x**i/factorial(i) for i in range(n+1))
def atans(x,n):
    return sum((-1)**i*x**(2*i+1)/(2*i+1) for i in range(n+1))

# Machin identity pi=16 atan(1/5)-4 atan(1/239), with alternating bounds.
p0=16*atans(Q(1,5),7)-4*atans(Q(1,239),6)
p1=16*atans(Q(1,5),6)-4*atans(Q(1,239),7)
assert Q("3.14159")<p0<p1<Q("3.14160")
assert series(Q(4),20)>Q("54.598")
assert Q("54.598")**2>2980
assert series(Q(6),7)>288
a=2154433
T=Q("14.583039")
assert Q("1467.798")**2<a and (a+1)**3<10**19
assert series(T,52)>a
t=Q("14.58")
r=t**53/factorial(53)/(1-t/54)
assert series(t,52)+r<a
assert 2980**3>2300000000
s,u,b,d=map(Q,("1.00054","1.000042",".91015","1.3999"))
assert 1+Q(8,5*2980)<s and 1+Q(1,8*2980)<u and s*u<Q("1.001")
assert d*u<Q("1.4")
for loss in (s*(8*b-d)/Q("54.598"), s*Q("1.001")*(b-d/12)/8,
             s*b*(Q("1.001")/16+Q(1,24))):
    assert Q(8,9)/u-loss>Q(".781")
for a0,L,r,c in [(2980,Q(8),Q("54.598"),Q(".2567")),
                (a,T,Q("1467.798"),Q(".03301"))]:
    assert (1+Q(1,a0))*L*(3*L-2+Q(3,a0))/(4*p0*r)<c
for a0,c in [(12,".208"),(400,".03301"),(2980,".012"),(1920,".0145"),(100,".065")]:
    assert (Q(19,30)+Q(26,25*a0))**2<a0*Q(c)**2
print("exact scalar checks passed")
