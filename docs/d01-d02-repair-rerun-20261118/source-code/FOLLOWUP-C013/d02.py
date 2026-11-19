#!/usr/bin/python3.10
"""Outward fixed-point certificate; all decisions integer/rational. See d02-proof.md."""
from verify import I,F, D, exp0, expb, log, hull, piB, v1,v2,v3,v4,vc,vJ, w, mini, lipart, S, fac, comb
from orders import coeff
from functools import lru_cache
import sys
H=3*10**12
h=log(H)
# Upper-decimal inputs from FKS Table 8, first subtable only.
rows=[(F('.75'),F('.80'),'7.798','4.101'),
      (F('.80'),F('.81'),'8.161','3.693'),(F('.81'),F('.82'),'8.538','3.613'),
      (F('.82'),F('.83'),'8.927','3.533'),(F('.83'),F('.84'),'9.330','3.453'),
      (F('.84'),F('.85'),'9.747','3.373'),(F('.85'),F('.86'),'10.176','3.293'),
      (F('.86'),F('.87'),'10.620','3.213'),(F('.87'),F('.88'),'11.076','3.133')]
B0=F(7,8); B2=F(27,32)
def aq(s):return 1-F(8,3)*(1-s),5-2*s
def cons(s):
 for a,b,c,d in rows:
  if a<=s<b:return I(c),I(d)
 raise ValueError(s)
def dz(s,h,c,d):
 a,q=aq(s);q=I(q)
 return 2*(c*expb(q*log(h)-a*h)/(a-q/h)+d*(h*h+2*h+2)*expb(-h))
def der(s):
 a,q=aq(s)
 return I(8)/3*h+2*log(h)+(I(8)/3+2/h)/(a-I(q)/h)
assert der(F('.75')).below(97) and der(F('.8')).below(92)
assert dz(B2,h,I('9.747'),I('3.693')).below('.149')
assert dz(B0,h,I('11.076'),I('3.693')).below('.0106')
assert dz(F('.80'),h,I('7.798'),I('4.101')).below('6.12')
assert (1/(18*piB)).below('.017684')
assert exp0(F(40,3)).above(51)
assert (exp0(20)-2).above(5*exp0(F(40,3)))
assert exp0(50).above(H)
# rho high strip +/- contributions. BH is rescaled by exp((1-beta)t).
def BHold(t,b):
 return I('.149' if b==B2 else '.0106')*t/(t-92)+I('6.12')*t/(t-97)*exp0(-(b-F('.8'))*t)
bands={}
for b in (B0,B2):
 bands[b]=[]
 for s,r,c,d in rows:
  if s>=b:break
  c,d=I(c),I(d);r=min(r,b)
  slope=F(-(-(100*der(s).b)//D),100)
  z=dz(r,h,c,d)
  bands[b].append((s,r,slope,z))
  if s==F('.87'):assert z.above('.0105')
  if s==F('.75'):assert r==F('.8')
z75=dz(F('.75'),h,I('7.798'),I('4.101'))
@lru_cache(None)
def BH(t,b):
 z=z75*exp0(-(b-F('.75'))*t)
 for s,r,d,v in bands[b]:
  ts=t-d
  assert ts>0
  z+=v*t/ts*exp0(-(b-r)*t)*(1-exp0(-ts*(r-s)))
 return mini(z,BHold(t,b))
# Residual with the entire absolutely converging high-strip sum in place of truncated one.
def rterms(t,b):
 yield (I('.017684')*t*t+I('1.865'))*exp0(-(b-F('.75'))*t),F('.25')
 yield I('2.091')*t*exp0(-(F(1,3)-(1-b))*t),F(1,3)
 for s,z,c,d in rows:
  if s>=b:break
  # Cut long band .75-.8 as well, and at beta.
  k=s
  while k<min(z,b):
   v=min(k+F('.01'),z,b)
   a,q=aq(k); L=I(t)/3
   # Remainder from remaining high zeros beyond exp(t/3).
   r=a/3+b-v; r2=F(1,3)+b-v
   yield 2*I(c)*expb(I(q)*log(L))*exp0(-r*t)/(a-I(q)/L),r+1-b
   yield 2*I(d)*(L*L+2*L+2)*exp0(-r2*t),r2+1-b
   k=v
def residual(t,b):
 return sum((e for e,r in rterms(t,b)),I())
def pp(t,b):
 return I('1.001')*exp0(-(b-F(1,2))*t)+I('2.67')*exp0(-(b-F(1,3))*t)
# Upper bound for log products and S multiplied by exp(alpha*t)*t;
# W upper bound after multiplication by exp(alpha*t).
def mcap(t,b,weighted):
 z=BH(t,b)*(1+I(1)/H*(1 if weighted else 1+I(1)/t))+pp(t,b)
 for e,r in rterms(t,b):
  r0=r-1+b
  # each residual term decreases at least exp(-lambda*(u-t)), lambda>alpha.
  lam=r0-F(7,2)/t # even L^2 polynomial and denominators covered
  assert lam>0
  z+=e*(1+(1 if weighted else 1+I(1)/t)/(1-b+lam))
 if not weighted: z=z/(1-z*exp0(-(1-b)*t)/t)
 return z
def Cth(t,b):
 return BH(t,b)+residual(t,b)+I('1.000000147')*exp0(-(b-F(1,2))*t)+I('1.78')*exp0(-(b-F(1,3))*t)
# Later sharper directional anchor choices. C constants computed outward and then frozen;
# v2 is a valid symmetric anchor at each of these logs.
anchors=(150,155,160,165,170,180,190,200,220,250,300,400,550,800)
@lru_cache(None)
def anc(a,b):
 c=Cth(a,b)
 # include the inherited errors for the anchor point
 base=mini(w(F(a),'1.06'),w(F(a),'-.97')) if a>=150 else v2(a)
 return c,base+c*exp0(-(1-b)*a)
@lru_cache(None)
def newv(t,b):
 return mini(*[c*(1+I(1)/(b-F(2,a))/t)*exp0(-(1-b)*t)+k*I(t)/a*exp0(a-t)
             for a in anchors if a<=t for c,k in (anc(a,b),)])
# Polynomial Li barriers (larger simultaneously certified order than in verify.py).
n=48;a=110
ls,g=lipart(I(a),440)
assert (g*a/441**2*2).below('1e-70')
X=(hull(-1,1)+log(a)+ls+hull(0,'1e-70'))*exp0(-a)
assert X.above(S(n,a)) and X.below(S(n,a)+2*I(fac(n+1))/a**(n+2))
assert (a*S(n,a)+2*I(fac(n+1))/a**(n+1)).below('1.01')
ll={i:fac(i-1) for i in range(1,n+2)}
uu=ll|{n+2:2*fac(n+1)}
P={}
for k in range(2,2*(n+2)+1):
 P[k-6]=sum(c*comb(k-2,i-1) for i,c in ll.items() if i<k)-sum(c*uu.get(k-i,0) for i,c in uu.items())
assert all(P[i]==0 for i in range(-4,0))
assert all(P[i]==coeff(i) for i in range(n-4))
def vanchor(l,r,b,side):
 return mini(w(l,side),newv(l,b)) if l>=150 else w(l,side)
def err(l,r,b,k):
 v=vanchor(l,r,b,'-.97')
 return I(r)**(k+4)*(I(r)/(l-1)*vanchor(l-1,r-1,b,'1.06')+v*(I('2.02')+v))
def resid(cs):
 return {j:F(c)-(F(cs[j]) if j<len(cs) else 0) for j,c in P.items() if j>=0}
def sl(l,r,ds,k,tail=False):
 v=I()
 for j,d in ds.items():
  if d==0:continue
  if tail:
   assert j>=k or d>=0
   if j>k and d>0:continue
   q=l
  else: q= (l if d>0 else r) if j<k else (r if d>0 else l)
  v+=I(d*F(q)**(k-j))
 return v
def tail(a,cs,k,b,verbose=True):
 a=F(a)
 assert a>=151 and a>1+(k+5)/(1-b)
 d=resid(cs)
 v=newv(a,b)
 e=I(a)**(k+4)*(I(a)/(a-1)*newv(a-1,b)+v*(I('2.02')+v))
 z=sl(a,a,d,k,True)-e
 if verbose: print('tail',str(b),str(a),k,cs[-1],z.fmt(),z.above(0))
 return z
def cells(a,A,cs,k,b,step=1):
 a,A=F(a),F(A); d=resid(cs)
 # True for endpoints: each error function chosen at left stays valid past right;
 # inherited branch switches split at 200,201,300,301.
 pts={a,A}|{F(k,step) for k in range(int(a*step)+1,int(A*step)+1) if a<F(k,step)<A}|{F(x) for x in (200,201,300,301) if a<x<A}
 zs=[sl(l,r,d,k)-err(l,r,b,k) for l,r in zip(sorted(pts),sorted(pts)[1:])]
 return mini(*zs)
def approx(z):return (z.a+z.b)/(2*D)
if __name__=='__main__' and 'explore' in sys.argv:
 for t in [150,155,160,165,170,175,180,185,190,200,220,250,300,400,550,800,1100]:
  print(t, ['%.6g'%approx(f(t,b)) for b in [B0,B2] for f in
             [BH,residual,lambda t,b:mcap(t,b,True),lambda t,b:mcap(t,b,False),newv]])
 for j in [2,3,4,5,6,7,8,9,10,11,12,15,18,19,20,24,28,32,37,43]:
  cs=[coeff(i) for i in range(j+1)]
  for b in [B0,B2]:
   for a in range(max(151,int(2+(j+6)/(1-b))),1600,2):
    if tail(a,cs,j+1,b,False).above(0):
     print('first search tail',j,b,a)
     break
