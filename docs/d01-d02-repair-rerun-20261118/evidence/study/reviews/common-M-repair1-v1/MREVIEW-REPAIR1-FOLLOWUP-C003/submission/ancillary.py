"""Exact review checks of interfaces of the unchanged candidate, not new estimates.
Run from the restored candidate directory:
PYTHONPATH=. /usr/bin/python3.10 /work/submission/ancillary.py /work/r0.stdout
"""
import sys
from pathlib import Path
from fractions import Fraction as F
from cert import I, exp, ln, count, qr
from mcert import W, rows, zc, dc
from repair_cert import zg, dg, qscaled

def both(i, lo, hi):
    assert i.above(lo) and i.below(hi), str(i)

t=I(100)
for k,c in [(F(1,4),F('.010')),(F(1,3),F('.018')),(F(2,5),F('.026'))]:
    T=exp(k*t)
    assert T.above(100) and ((exp(t/2)-2)/5-T).above(0)
    a2=F('.16')*k*k-c
    a1=-F('.26')*k
    assert a2 <= 0 and a1 < 0 and a2*100**2+a1*100+F('.98') < 0
assert exp(1).above('2.45') and exp(58).below(2169*10**22)
assert exp(I('36.713')).below(115*10**14)
assert exp(I('39.47')).below(139*10**15)
v=ln(2); ei=I(-1,1)+ln(v); term=I(1)
# sincelog(2)<1 use the same exponential tail comparison.
for j in range(1,13):
    term=term*v/j
    ei+=term/j
from math import factorial
ei+=I(0,F(2,factorial(13)))
both(2/v-ei,-10,10)
# Positive denominator on the entire old spectral domain L>=100.
Z=zc(t);d=dc(t)
bh=(1+I(F(2,3*10**12))*(1+1/t))*Z+(9+8/t)*d+3*exp(-7*t/8)
assert (1-bh*exp(-t/8)/t).above(0)
# Exact strict gains in two bounding functions at a matched argument,
# not claims of all-ray dominance.
v=I(200)
assert (qr(v)*exp(v/8)-qscaled(v)).above(0)
assert (zc(v)-zg(v)).above(0)
for k in (F(1,3),F(2,5)):
    for s,hi,_,_ in rows:
        q=5-2*F(s); al=(8*F(s)-5)/3
        assert al-q/(100*k)>0
        assert q/(k*100**2)/(al-q/(100*k))<F('.01')
        assert F(7,8)-k*al-(F(7,8)-F(hi))-F('.02')-F('.01')>F(1,4)
print('cutoff domains, ordinate quadratics, source joins, history constant, spectral positivity and example gains checked')
# Show the signed R counterexample and its corresponding positive bracket end.
A=38358837682
cm=count(A); cn=count(14111427770)
assert (cm,cn)==(1644673232,632207037)
for d,lo,hi in [('0.21792','-900','-100'),('0.21794','100','2000')]:
    x=A+I(d)
    gap=exp(1)*x*cn/ln(x)-cm**2
    both(gap,lo,hi)
    print('R(A+'+d+') in',gap)
# Derivative/sign checks on the full frozen unit cells, not just root brackets.
lines=Path(sys.argv[1]).read_text().splitlines()
D=int(lines[0].split()[-1]); assert D==2**56
iv=lambda a,b:I(F(a,D),F(b,D))
g0,g1,m0,m1,b0,b1=map(int,lines[1].split())
g,m,B=iv(g0,g1),iv(m0,m1),iv(b0,b1)
w={}
for line in lines[2:]:
    if line.startswith('witness'):
        n,rec=line.split(': ')
        w[int(n.split()[-1])]=list(map(int,rec.split()))
for k,n in [('H',2278382),('Q',2278381),('P',2278381),('S',912559)]:
    _,_,_,_,a,A,q,Q,s,T=w[n]
    L=ln(I(n,n+1))
    if k=='H':
        z=iv(a,A)-m-ln(L); deriv=3*z-1
    elif k in ('Q','P'):
        z=iv(q,Q)-g-ln(L)
        deriv=2*exp(z)-3 if k=='Q' else 3-4*exp(-z)
    else:
        z=iv(s,T)+B-L; deriv=2*L*z-L**2
    assert z.above(0) and deriv.below(0)
    print(k,'strict positivity before next jump and negative derivative factor on',n,n+1)
# Illustrate the failed .039 analytic sufficient check, not a violation of D2.
L=I('22.1'); r=I('22.12'); b=I('29.9')
from cert import PI
B=2*(b*b+4*b+8)*exp(-b/2)/(8*PI)+I('2.1e-10')
cell=r*r*(I('3.4511')*exp(-L/2)+B-I('3.66')*exp(-b/2))
both(cell,'.039','.0391')
print('22.1 first cell upper-bound expression, not actual error:',cell)
