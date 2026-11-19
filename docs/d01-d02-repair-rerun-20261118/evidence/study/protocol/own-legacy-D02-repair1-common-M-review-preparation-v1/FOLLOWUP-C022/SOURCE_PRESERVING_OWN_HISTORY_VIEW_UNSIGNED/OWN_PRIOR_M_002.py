"""Ancillary exact tests of written inequalities, no new search or algorithm."""
import ast, os
from fractions import Fraction as F
from pathlib import Path
from d02screen import *
import d02ram as r
import d02m as m
import endpoint_check as er
import mertens_check as ms
from extra_check import grid,loss,TAIL
import portfolio_check as p
from d02rigor import I
N=38358837682; x=N+F(1,10); l,u=er.lu(x); el,eu=er.ei(F(1))
q=632207037; P=1644673232
g=(el*x*q/u-P*P,eu*x*q/l-P*P)
assert -8100000<g[0]<=g[1]<-7900000
print('R(N+1/10) between -8100000 and -7900000',flush=True)
y=912560;f=ms.sieve(y);s=(0,)*6
for q in range(2,y+1):
    if f[q]:s,_,_=ms.add(s,q)
txt=Path(os.environ.get('MERT_REPLAY','/work/receipts/mertens_check.out')).read_text()
G,M,C=ast.literal_eval('('+txt.splitlines()[1].split(': ',1)[1].replace(') (','),(')+')')
L=ms.lp_data(y); ll,uu=ms.residuals(s,s,L,L,(*M,*C))[2]
lo,hi=F(ll*L[0]**2,ms.B**3),F(uu*L[1]**2,ms.B**3)
assert F('.2999993')<lo<=hi<F('.2999995')
print('V scaled at 912560 in (.2999993,.2999995)',flush=True)
for i,j,z in [(50,58,F(1,8)),(58,100,F(1,4)),(100,169,F(1,4))]:
    for l,u in grid(F(i),F(j),z):
        assert 85+1412/u-TAIL/l**7>u**6*loss(l,u,'C')
print('R K=60 through 169, original non-QRH check',flush=True)
for mode in (False,True):
    p.DUSART_ONLY=mode;p.Z=None;p.spectral.cache_clear()
    p.spectral(F(180))
    assert p.Z[-1]*(1+1/p.H)<p.I('.00673')
p.DUSART_ONLY=False;p.Z=None;p.spectral.cache_clear()
assert 5*e(50)+2<e(100) and e(50)>200
assert 5*e(81)+2<e(90) and e(81)>180
t=F('167.656');x=I(t)
def sr(L):
    x=I(L); J,J2=m.smooth(L)
    return (1+1/x)*J+2*(1/x+2/x**2)*J2+I('2.000000294')*e(-(F(1,2)-a)*x)+I('2.67')*e(-(F(2,3)-a)*x)+x*e(-b*x)
def flat(L):
    x=I(L)
    return 2*e(a*x)*(A0+117*e(-x/2))**2
assert screen(t,c=F(7,20))+3*e(-(F(1,2)-a)*x)<I('.26')
z=maxI(maxI(flat(F(155)),flat(t))+sr(F(155)),2*I('.26')**2*e(-a*x)+sr(t))
print('Using the written factor 2 and the lawful .26 cap at the fixed join:',z,flush=True)
# For |w|<=.01 and L>=155 the two logarithm remainders total < w^2/L.
assert 1/(2*I('.99'))+1/(2*I('.99')**2*155*(1-I('.01')/(I('.99')*155)))<1
assert A0+117*e(-I(155)/2)<I('.01') and I('.26')*e(-a*x)<I('.01')
z=maxI(maxI(flat(F(155)),flat(t))/2+sr(F(155)),I('.26')**2*e(-a*x)+sr(t))
assert z/(1-z*e(-155*a)/155)<I('6e-13')
print('Primorial with elementary log-remainder check and legal .26 cap:',z,flush=True)
assert r.spi(F(191))*e(a*I(191))<I('.24')
assert r.spi(F(535))*e(a*I(535))<I('.144')
assert I('.249146')*e(-I(175)/32)<I('.00666')
assert I('.249146')*e(-I(175)*a)<A0
assert r.spi(F(175))*e(a*I(175))<I('.248')
assert I('.248')*e(-I(175)/32)<I('.00666')
assert I('.248')*e(-I(175)*a)<A0
p.spectral(F(180))
assert I(p.Z[-1].L())>I('.00666')
assert scr2(F(180))*e(-I(180)/32)<I('.00666')/I(p.H.U())
print('Arbitrary-order count cap at actual earliest argument 191 and signed-smoothed comparison',flush=True)
for c in (F('.0014'),F('.0015')):
    for L in (F('59.5'),):
        assert maxI(m.convexbridge(L,t,F(1,8),0),m.combined(t)*e((F(1,8)-a)*x))<I(c)
print('D02 old-shape .0014/.0015 tails; finite joins recycled unchanged',flush=True)
# For second shifted bound in L^6 units: subtract its target L+69
# and its own cost, using the same denominator as the locked certificate.
worst=None
for l,u,h0 in [(58,154,'.25'),(154,167,'.025'),(167,172,'.02')]:
    for ll,rr in grid(F(l),F(u),F(h0)):
        # combined upper cost+target = 69 + (13v+4/L^3)/(1-v/L).
        X=I(ll);v=1+4/X**4
        cost=69+(13*v+4/X**3)/(1-v/X)
        g=r.polyr(rr,6,17)-r.loss(ll,rr,6,17,shift=F('1.001'))-r.qerr(ll,rr,6,17)-cost
        if worst is None or g.lo<worst[0].lo:worst=(g,ll,rr)
print('Second shifted min reserve and cell:',worst, flush=True)
X=I(172);v=1+4/X**4
assert I(145)-r.loss(F(172),F(172),6,17,tail=True,shift=F('1.001'))-r.qerr(F(172),F(172),6,17)-69-(13*v+4/X**3)/(1-v/X)>0
