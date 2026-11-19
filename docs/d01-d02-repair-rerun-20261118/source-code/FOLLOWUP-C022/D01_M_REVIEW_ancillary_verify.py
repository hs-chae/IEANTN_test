"""Directed ancillary checks; run with PYTHONPATH=/work/exact019 from that directory."""
import ast, os
from pathlib import Path
from fractions import Fraction as F
from endpoint_check import lu, ei
from mertens_check import sieve,add,lp_data,residuals,B
from portfolio_check import I,e,cres,spectral, Z
from rigor import PI
d=Path(os.getenv('REVIEW_EVIDENCE_DIR','/work/submission'))
N=38358837682
x=N+F(1,10); l,u=lu(x); el,eu=ei(F(1))
q=632207037; p=1644673232
g=(el*x*q/u-p*p,eu*x*q/l-p*p)
assert -8100000<g[0]<=g[1]<-7900000
print('R(N+1/10) is strictly between -8100000 and -7900000')
a=I(20)
r=2*a*e(-a/2)/(8*PI)+1354*a*e(-a)
assert r<40*a*e(10-a)/(8*PI)
assert e(I('28.15'))<10**13 and e(I('28.15'))>10**11
assert 5*e(50)+2<e(100) and e(50)>200
assert 5*e(81)+2<e(90) and e(81)>180
assert e(I('59.5'))>2*10**25
print('anchors, source ranges and truncation starting inequalities passed')
x=912560
s=sieve(x)
state=(0,)*6
for p in range(2,x+1):
    if s[p]: state,_,_=add(state,p)
G,M,C=ast.literal_eval('('+ (d/'Msieve.stdout').read_text().splitlines()[1].split(': ',1)[1].replace(') (','),(')+')')
L=lp_data(x)
l,u=residuals(state,state,L,L,(*M,*C))[2]
lo,hi=F(l*L[0]**2,B**3),F(u*L[1]**2,B**3)
assert F('.2999993')<lo<=hi<F('.2999995')
print('weighted scaled error at 912560 strictly between .2999993 and .2999995')

from ray_check import grid,loss,TAIL
for a,b,step in [(50,58,F(1,8)),(58,100,F(1,4)),(100,169,F(1,4))]:
    for l,r in grid(F(a),F(b),step):
        assert 85+1412/r-TAIL/l**7>r**6*loss(l,r,'C')
print('Historical QRH-free 60/L^2 bounded profile replay passed')
import portfolio_check as pc
for mode in (False,True):
    pc.DUSART_ONLY=mode; pc.Z=None; pc.spectral.cache_clear()
    pc.spectral(F(180))
    assert pc.Z[-1]*(1+1/pc.H)<I('.00673')
print('limiting-coefficient slack including 1/H passed (both variants)')
