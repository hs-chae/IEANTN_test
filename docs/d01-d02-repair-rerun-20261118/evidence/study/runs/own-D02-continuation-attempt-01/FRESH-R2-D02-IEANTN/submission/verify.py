#!/usr/bin/python3.10
"""Exact outward fixed-point verification. No floating point is used for decisions."""
from math import factorial as fac, comb, isqrt
from fractions import Fraction
from functools import lru_cache
D=1<<384
class I:
 def __init__(self,x=0):
  if isinstance(x,I): self.a,self.b=x.a,x.b; return
  r=Fraction(x)*D
  self.a=r.numerator//r.denominator; self.b=-((-r.numerator)//r.denominator)
 @classmethod
 def raw(cls,a,b):
  z=object.__new__(cls);z.a,z.b=a,b;return z
 def __add__(x,y):
  y=I(y);return I.raw(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I.raw(-x.b,-x.a)
 def __sub__(x,y):return x+-I(y)
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  y=I(y); z=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b]
  return I.raw(min(z)//D,-(-max(z)//D))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=I(y);assert y.a>0
  return x*I.raw(D*D//y.b,-(-(D*D)//y.a))
 def __rtruediv__(x,y):return I(y)/x
 def __pow__(x,n):
  if n<0:return 1/x**(-n)
  r=I(1)
  while n:
   if n&1:r=r*x
   n//=2
   if n:x=x*x
  return r
 def above(x,y):return x.a>I(y).b
 def below(x,y):return x.b<I(y).a
 def fmt(x):
  return '%.12g..%.12g'%(x.a/D,x.b/D) # display only
def hull(a,b):return I.raw(I(a).a,I(b).b)
def mini(*s):return I.raw(min(x.a for x in s),min(x.b for x in s))
@lru_cache(None)
def exp0(t):
 return expb(I(t))
def expb(x):
 if x.a!=x.b: # monotone endpoint reduction, endpoints are exact dyadics
  return I.raw(exact_exp(I.raw(x.a,x.a)).a,exact_exp(I.raw(x.b,x.b)).b)
 return exact_exp(x)
def exact_exp(x):
 z=0
 while max(abs(x.a),abs(x.b))>D//2:
  x=x/2;z+=1
 s=t=I(1)
 for k in range(1,49):
  t=t*x/k;s=s+t
 # |remainder| <= 2/(2^49 * 49!) < 2^-250
 s=s+hull(-Fraction(1,1<<250),Fraction(1,1<<250))
 for _ in range(z):s=s*s
 return s
def redlog(y):
 z=(y-1)/(y+1);q=z*z;s=I(0);t=z
 assert z.b<=D//3+3 and z.a>=-3
 for j in range(100):
  s=s+t/(2*j+1);t=t*q
 return 2*s+hull(-Fraction(1,1<<300),Fraction(1,1<<300))
LG2=redlog(I(2))
def log(x):
 x=I(x)
 assert x.a>0
 def one(a):
  n=a.bit_length()-D.bit_length()
  d=I(Fraction(a,D)/(Fraction(2)**n))
  return redlog(d)+n*LG2
 return I.raw(one(x.a).a,one(x.b).b)
def ech(t,r):
 # t here is rational, not an interval
 return exp0(r*t)
# Elementary checks supporting constants.
assert log(600).above(6) and log(600).below(7)
assert exp0(Fraction('39.47')).below(139000000000000000)
assert exp0(58).below(21690000000000000000000000)
assert exp0(21).above(10**9)
# density constants, safe apart from exactly the inherited Corollary/Table stated in paper
h=log(3*10**12)
den=I(7)/15-I('3.4')/h
assert (I(8)/3*h+2*log(h)+(I(8)/3+2/h)/den).below(92)
b0=2*(I('11.076')*expb(I('3.25')*log(h)-I(2)/3*h)/(I(2)/3-I('3.25')/h)+I('3.693')*(h*h+2*h+2)/(3*10**12))
assert b0.below('.0106')

def dens(t):
 return I('.0106')*t/(t-92)+(I('.01')*t*t+I('1.865'))*ech(t,Fraction(-3,40))+I('2.091')*t*ech(t,Fraction(-1,8))
for t,c in [(200,'.021'),(250,'.017'),(300,'.016'),(800,'.012')]:
 assert dens(t).below(c)
for t in [200]:
 assert exp0(Fraction(t,4)).above(max(51,t))
 assert (exp0(Fraction(t,2))-2).above(5*exp0(Fraction(t,4)))
assert (I('.021')+I('1.001')*exp0(-75)+I('1.78')*exp0(Fraction(-325,3))).below('.022')
assert (I('1.05e-12')*(1+I('1.04')/200)+(115+I(248)/200)*exp0(-100)+I('7e-11')*200/58*exp0(-142)+I('.022')*exp0(-25)).below('1.5e-12')
def v1(t):
 return I('.039789')*(t*t+2*t)*ech(t,Fraction(-1,2))+5*t*ech(t,-1)
assert I('.039789').above(1/(8*I('3.1415926')))
assert (v1(58)+I('1.05e-12')+115*exp0(-29)).below('7e-11')
def lipart(t,N):
 z=I(1);s=I()
 for j in range(1,N+1):
  z=z*t/j;s+=z/j
 return s,z
pr=[p for p in range(2,601) if all(p%d for d in range(2,isqrt(p)+1))]
lb=log(600)
ls,lterm=lipart(lb,100)
assert (lterm*lb/101**2*2).below('1e-70')
Q=109-(log(lb)+ls+hull(-1,I(1)+I('1e-70')))-(sum((log(p) for p in pr),I())-600)/lb
assert len(pr)==109 and Q.above(-5) and Q.below(5)
piB=hull('3.1415926535','3.1415926536')
def arct(q):
 z=sum((I((-1)**j)/((2*j+1)*q**(2*j+1)) for j in range(20)),I())
 return z+hull(0,Fraction(1,41*q**41))
pi_chk=16*arct(5)-4*arct(239)
assert pi_chk.above('3.1415926535') and pi_chk.below('3.1415926536')
assert exp0(Fraction('36.75')).below(11500000000000000)
Ts=[10**7,15*10**6,20*10**6,25*10**6,30*10**6,45*10**6,60*10**6,80*10**6,10**8,120*10**6]
tc=[]
for T in Ts:
 u=log(I(T)/(2*piB)); C=(u*u-u/3)/(2*piB)
 A=piB/(T-1)+I('3.3')/T**2
 K=v1(21)+A+(C+I('1.06'))*exp0(Fraction(-21,2))
 tc.append((A,C,K))
@lru_cache(None)
def vc(t,side):
 return mini(*[A*(1+I('1.11')/t)+(C+I(side))*(1+I('2.48')/t)*ech(t,Fraction(-1,2))+K*t/21*exp0(21-t) for A,C,K in tc])
def Jcor(t):
 return (I(1)+I(2)/t+I('10.15264')/t**2+I('1.2551')*(exp0(Fraction(-t,6))+I(t)/I('.69')*exp0(Fraction(-t,4))))
assert log(2).above('.69')
assert Jcor(21).below('1.4') and Jcor(35).below('1.08')
assert (I('.039789')*(58+21+(58**2-21**2)/4+58-21)).below(50)
@lru_cache(None)
def vJ(t,side):
 c=I('1.08' if side=='1.06' else '-1')
 return mini(*[A+(C+c)*ech(t,Fraction(-1,2))+
         (v1(21)+I('1.4')*exp0(Fraction(-21,2))+A+C*exp0(Fraction(-21,2))+1050*exp0(-21))*t/21*exp0(21-t)
         for A,C,K in tc])
def v2(t):
 return I('1.05e-12')*(1+I('1.04')/t)+(115+I(248)/t)*ech(t,Fraction(-1,2))+I('7e-11')*t/58*exp0(58-t)
def v3(t):
 return I('.022')*(1+I('1.16')/t)*ech(t,Fraction(-1,8))+I('1.5e-12')*t/200*exp0(200-t)
def v4(t):
 return I('.0161')*(1+I('1.16')/t)*ech(t,Fraction(-1,8))+I('2e-18')*t/300*exp0(300-t)
assert (v3(300)+I('.0161')*exp0(Fraction(-300,8))).below('2e-18')
assert (I('.016')+I('1.001')*exp0(Fraction(-900,8))+I('1.78')*exp0(Fraction(-975,6))).below('.0161')
# Exponential barrier for Ei, simultaneously lower and upper.
def S(n,t):return sum((I(fac(j))/t**(j+1) for j in range(n+1)),I())
a=35;n=24
ss=I(); g=I(1)
for j in range(1,181):
 g=g*a/j;ss+=g/j
assert (g*35/181/181*2).below('1e-40')
anchor=(hull(-1,1)+log(a)+ss+hull(0,'1e-40'))*exp0(-a)
assert anchor.above(S(n,a)) and anchor.below(S(n,a)+I(5*fac(n+1))/a**(n+2))
lc=[0]+[fac(j) for j in range(n+1)]
up=lc+[5*fac(n+1)]
poly={}
for k in range(2,53):
 d=sum(lc[i]*comb(k-2,i-1) for i in range(1,min(n+1,k-1)+1))
 d-=sum(up[i]*up[k-i] for i in range(1,len(up)) if 1<=k-i<len(up))
 poly[k-6]=d
assert [poly[j] for j in range(-4,7)]==[0,0,0,0,1,14,145,1412,13985,145450,1610021]
assert (36*S(n,36)+I(5*fac(n+1))/36**(n+1)).below('1.04')
def lowpoly(l,r):
 return sum((I(c)/((r if c>=0 else l)**j) for j,c in poly.items() if j>=0),I())
assert (sum((I(-c)/400**(j-6) for j,c in poly.items() if c<0),I())).below(10021)
# Each v majorant is decreasing over its use interval; retain CH2 or finite RH where useful.
from fractions import Fraction as F
@lru_cache(None)
def w(t,side):
 b=v1(t) if t<58 else v2(t)
 if 21<=t<=75:b=mini(b,vc(t,side))
 if 35<=t<58:b=mini(b,vJ(t,side))
 if t>=200:b=mini(b,v3(t))
 if t>=300:b=mini(b,v4(t))
 return b

def low_res(l,r,cs,scale):
 d=poly.copy()
 for j,c in enumerate(cs):d[j]-=F(c)
 return sum((I(c)/I(r if c>=0 else l)**(j-scale) if j>=scale else I(c)*I(l if c>=0 else r)**(scale-j)
             for j,c in d.items() if j>=0 and c),I())

def cellerr(l,r,scale):
 z=I(r)
 d=z**(5+scale)/(l-1)*w(l-1,'1.06')
 if r>F('39.47'):
  q=w(l,'-.97');d+=z**(4+scale)*q*(I('2.08')+q)
 return d

def gap_cert(a,b,cs,den=40,scale=0):
 a,b=F(a),F(b)
 rs=[a]+[F(k,den) for k in range(int(a*den)+1,int(b*den)+1) if a<F(k,den)<b]+[b]
 rs=sorted(set(rs+[x for x in map(F,[35,36,58,59,75,76,200,201,300,301,'39.47']) if a<x<b]))
 mm=None
 for l,r in zip(rs,rs[1:]):
  margin=low_res(l,r,cs,scale)-cellerr(l,r,scale)
  if not margin.above(0):raise AssertionError((a,b,cs,l,r,margin.fmt()))
  mm=margin if mm is None else mini(mm,margin)
 print('gap',a,b,cs,'slack',mm.fmt())

def tail(a,cs,scale):
 # Positive terms with j>scale discarded. Negative terms j>=scale evaluated at a.
 d=poly.copy()
 for j,c in enumerate(cs):d[j]-=F(c)
 assert all(c>=0 for j,c in d.items() if 0<=j<scale)
 val=sum((I(c)/I(a)**(j-scale) for j,c in d.items() if 0<=j<=scale or c<0 and j>scale),I())
 # replace rational factor 1/(L-1) by (a/(a-1))/L
 z=I(a);q=v4(a)
 err=z**(4+scale)*(z/(a-1)*v4(a-1)+q*(I('2.08')+q))
 assert F(a)>max(301,8*(scale+5)+1)
 assert val.above(err),(a,cs,scale,val.fmt(),err.fmt())
 print('tail',a,cs,'slack',(val-err).fmt())
# Finite near the last integer: combinatorial divisor sieve at quotient values.
def primepi(n):
 i=isqrt(n)
 vals=[n//j for j in range(1,i+1)]
 vals+=list(range(vals[-1]-1,0,-1))
 v={k:k-1 for k in vals}
 for p in range(2,i+1):
  if v[p]>v[p-1]:
   base=v[p-1]
   for k in vals:
    if k<p*p:break
    v[k]-=v[k//p]-base
 return v[n]
def root():
 x=38358837682; e=exp0(1)
 assert (x/e).above(14111427770) and ((x+1)/e).below(14111427771)
 a=primepi(x);b=primepi(14111427770)
 assert (a,b)==(1644673232,632207037)
 def R(y):return e*y*b/log(y)-a*a
 assert R(I(x)+I('.21792636')).below(0)
 assert R(I(x)+I('.21792637')).above(0)
 rr=R(x)
 print('last counterexample bracket verified; R(integer)=',rr.fmt())

if __name__=='__main__':
 import sys
 if 'root' in sys.argv:root()
 if 'trade' in sys.argv:
  for a,b,c in [('36.60','36.75','0'),('36.70','36.8','.065'),('36.8',37,'.10'),('36.99',37,'.20'),('39.61','39.7','.25'),('40.5',41,'.50'),
                ('41.93',42,'.80'),('43.16','43.2','1')]:
   try:gap_cert(a,b,[c],200,0)
   except AssertionError as e:print('unverified:',e)
  tail(850,[poly[j] for j in range(19)]+[15700000000000000000000],19)
 if 'gap' in sys.argv:
  for a,b,c,den,scale in [
    ('36.75','36.8',[0],80,0),('36.8','37',['.03'],160,0),
    ('37','39.47',['.21'],160,0),('37.2','39.47',['.29'],160,0),
    ('37.3','39.47',['.33'],160,0),('38','39.47',['.57'],160,0),
    ('39','39.47',['.82'],160,0),('39.47','39.7',['.20'],200,0),
    ('39.7',40,['.27'],80,0),('40',41,['.385'],80,0),
    ('41',42,['.64'],80,0),('42',43,['.815'],80,0),
    ('43','43.2',['.979'],100,0),('43.2',49,[1],80,0),
    ('45',65,['1.18'],40,0),('46',60,['1.24'],40,0),
    ('48',59,['1.28'],40,0),('49',400,[1,'13.69'],10,1),
    ('55',145,[1,14,115],10,2),('55',175,[1,14,40],10,2),
    ('62',106,[1,14,145,1000],20,3),
    ('215',400,[1,14,120],10,2),('240',400,[1,14,145,850],20,3),
    ('265',400,[1,14,145,1412,7000],20,4),
    ('300',400,[1,14,145,1412,13985],20,5),
    ('325',400,[1,14,145,1412,13985,145450],20,6)
  ]:
   try:gap_cert(a,b,c,den,scale)
   except AssertionError as e:print('unverified:',e)
  for a,c,k in [(400,[1,14,145,1412,13985,145450,1500000],6),
                (550,[poly[j] for j in range(12)],12),
                (850,[poly[j] for j in range(19)],19)]:
   try:tail(a,c,k)
   except AssertionError as e: print('unverified tail:',e)
