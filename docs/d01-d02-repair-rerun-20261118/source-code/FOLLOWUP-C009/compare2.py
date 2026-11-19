"""Matched Taylor coefficients and certified rational onsets."""
from higher2 import poly, best, active, uN, aN
from spectral import I,F,S,profile,b0,b2,exp,ceil,floor
from joins2 import short_plateau
from cert import I as C,S as CS,exp as exp0,ch,qr
from repair_cert import qscaled

def lift(a):
 return I(F(a.a,CS),F(a.b,CS))
def minball(*xs):
 return I(min(x.a for x in xs),min(x.b for x in xs),True)
def r(v,b):
 q=profile(v,b)[-1]
 p=q*exp(-(1-b)*I(v))
 w=C(v)
 old=ch(w)
 new=short_plateau(v)
 known=qscaled(w)*exp0(-w/8)
 return minball(p,lift(old),lift(new),lift(known),lift(qr(w)))

def margin(a,b):
 n=48;t=I(a)
 p=poly(n);x=r(a,b);y=r(a-1,b)
 # lower bound minus 1+14/L, scaled by L^2
 K=sum(p[j]/t**(j-6) for j in range(6,len(p)))
 val=K-t**6*(t/(t-1)*y+(2*uN(t,n)+x)*x)
 return floor(val,1000),ceil(val,1000)

def real(k,c,b):
 j0,n,j=best(k,c,b)
 lo=100*(j0-1)
 hi=100*j0
 # only reduce if all domain / monotonicity prerequisites already hold
 lo=max(lo,int(100*max(151,8*j+1,2*n+6)))
 while lo<hi:
  m=(lo+hi)//2
  if active(F(m,100),n,k,j,c,b):hi=m
  else:lo=m+1
 p=F(lo,100)
 assert active(p,n,k,j,c,b)
 return p,n,j

if __name__=='__main__':
 for a in (150,160,165,168,170,175,180,190,200,220,250,500):
  print('paired margin coefficient brackets at',a,margin(a,b0),margin(a,b2),flush=True)
 for k,c in [(6,F('97.5'))]+[(k,poly(128)[k]) for k in (6,7,8,12,16,24,31,32,48,64,96,127)]:
  p=real(k,c,b0);q=real(k,c,b2)
  assert q[0]<p[0]
  print('rational k and c (exact if -), B0 a,N,j, D02 a,N,j',k,'-' if c==poly(128)[k] else c,p,q,flush=True)
