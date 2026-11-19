"""Ancillary checks only. Run from /work/review-candidate with PYTHONPATH=. .
No change to original sources, onsets, coefficients, or finite-cell algorithm."""
import sys
from subprocess import run
import verify as v
import model as m
from interval import *
from math import factorial
Q=Fraction

def estimate(z): return (float(Q(z.a,S)),float(Q(z.b,S)))
# PT 2004 PDF p.4 PDF content object 114 prints log squared in the pi line.
# Verify the two SPECIFIC stronger anchor inequalities from other permitted
# facts, using the same submitted partial summation and prime counting.
a=38358837682
pc_rows=run([sys.argv[1]],input='38358837682\n38358837683\n14111427770\n',text=True,check=True,capture_output=True).stdout
assert [tuple(map(int,row.split())) for row in pc_rows.splitlines()]==[(a,1644673232),(a+1,1644673232),(14111427770,632207037)]
for n in (a,a+1):
    f=I(n)/ex(1)
    assert 14111427770*S<f.a<=f.b<14111427771*S
x=Q('38358837682.1')
R=632207037*ex(1)*x/ln(x)-1644673232**2
assert R.b<0
print('real counterexample',x,estimate(R),flush=True)
e16=ex(16)
n=e16.a//S
assert n==e16.b//S
stdout=run([sys.argv[1]],input=str(n)+'\n',text=True,check=True,capture_output=True).stdout
n1,pi=map(int,stdout.split());assert n1==n
li=v.li_anchor(Q(16))
d=16/ex(16)*(pi-li)
cap=m.pe(Q(16),-1)
assert (cap+d).yes() and (cap-d).yes()
print('16 anchor count',stdout.strip(),'signed normalized deviation',estimate(d),'cap',estimate(cap),flush=True)
# From log 40 to 58: printed finite-RH Corollary 1 pi error uses log^2
# before normalization, theta uses log^2. For z use CH + power correction.
u,t=Q(58),Q(40)
anch=(t*t+t)/m.PI8
radius=anch*u*ex(t/2-u)+sum(c*m.weight(u,d,a)*(1+1/(u*(1-a-2/t))) for c,d,a in m.CH+m.POWER)
cap=m.pe(u,-1)
assert (cap-radius).yes()
print('58 anchor valid normalized radius',estimate(radius),'cap',estimate(cap),flush=True)

# Genuine source inequality (u/1 times the locked finite normalized bound)
# on u<=58, valid E for u>58 as just checked.
orig=m.pe
def pe(u,method):
    return u*orig(u,-1) if method==-1 else orig(u,method)
m.pe=pe
def test(k,on,c,b,end=320):
    on,c,end=Q(on),Q(c),Q(end)
    xs=sorted({on,end}|{Q(j,20) for j in range(int(on*20)+1,int(end*20)+1)})
    def cell(a,z,depth):
        if (m.lower(a,z,b,k)-c).yes():return
        if not depth:raise ValueError((a,z))
        mid=(a+z)/2
        cell(a,mid,depth-1);cell(mid,z,depth-1)
    for a,z in zip(xs,xs[1:]):
        try:cell(a,z,12)
        except ValueError as exc:return ('failed sufficient test',str(exc.args[0]))
    return ('passes',)
for b,k,on,c in v.ROWS:
    if Q(on)<59: print('printed finite branch',b,k,on,c,test(k,on,c,b,59),flush=True)
print('sign join [58,59]',test(0,58,0,0,59),flush=True)
# On L>=59 the locked numerical checks are applicable without changing
# their formulas: only u=58 itself is used there in the finite branch,
# and the actual stronger bound at that point was just verified.
