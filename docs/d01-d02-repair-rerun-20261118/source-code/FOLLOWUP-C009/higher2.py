"""Paired Taylor-ray searches with exact scaled tests and monotone continuation."""
from functools import lru_cache
from dyad import I,F,S,exp,ln,f,comb
from spectral import profile,b0,b2,ceil,choose
from cert import ch

NS=(16,32,48,64,96,128)
BASES=(100,150,160,165,170,175,180,185,190,200,250,300,500,1000,5000)
def aN(t,n):
 return sum(f(i)/t**i for i in range(n+1))
def uN(t,n):
 return aN(t,n)+3*f(n+1)/t**(n+1)
def anchor(n):
 t=2*n+5
 J=6*t
 w=I(1);p=ln(t)+I(-1,1)
 for j in range(1,J+1):
  w=w*t/j;p+=w/j
 p+=I(0,F(2*t**(J+1),f(J+1)))
 scaled=p*t/exp(t)
 assert (scaled-aN(I(t),n)).above(0)
 assert (uN(I(t),n)-scaled).above(0)
 print('anchor N,v',n,t,flush=True)
 return t

@lru_cache(None)
def poly(n):
 cs=[sum(f(i)*comb(j,i) for i in range(min(n,j)+1)) for j in range(2*n+3)]
 u=[f(i) for i in range(n+1)]+[3*f(n+1)]
 for i,x in enumerate(u):
  for j,y in enumerate(u):cs[i+j]-=x*y
 assert cs[:6]==[0,0,0,0,1,14]
 assert min(cs[4:n+1])>0
 return cs

@lru_cache(None)
def tab(b):
 return tuple((v,ceil(profile(v,b)[-1],10**7)) for v in BASES)
def Q(v,b):
 return next(c for a,c in reversed(tab(b)) if v>=a)

def taylor_loss(a,n,j,b):
 # Frozen coefficient Q but use errors at separate arguments.
 t=I(a);B=Q(a-1,b);C=Q(a,b);D=1-b
 e=C*exp(-D*t)
 E=exp(j*ln(t)-D*t)
 return E*(exp(D)*B*t/(t-1)+C*(2*uN(t,n)+e))

@lru_cache(None)
def active(a,n,k,j,c,b):
 cs=poly(n)
 rhs=(cs[k]-c)*a**(j-k)+sum(cs[i]*a**(j-i) for i in range(k+1,j+1))
 neg=sum(F(-cs[i],a**(i-j)) for i in range(j+1,len(cs)) if cs[i]<0)
 return (I(rhs-neg)-taylor_loss(a,n,j,b)).above(0)

def first(n,k,j,c,b):
 lo=max(151,8*j+1,2*n+6);hi=7000
 assert active(hi,n,k,j,c,b)
 while lo<hi:
  m=(lo+hi)//2
  if active(m,n,k,j,c,b):hi=m
  else:lo=m+1
 assert active(lo,n,k,j,c,b)
 return lo

def best(k,c,b):
 # Trying all N is unnecessary when there are many established positive
 # future coefficients. The anchor tradeoff still includes 2 choices.
 ns=[n for n in NS if n>=k]
 ns=ns[:2]
 return min((first(n,k,j,c,b),n,j) for n in ns
          for j in range(k+(c==poly(n)[k]),min(n,k+4)+1))
def show(b,c1,names):
 print('frozen Q',b,*tab(b),flush=True)
 if not names:return
 for c in (0,40,80,100,F('97.5'),120,130,140,143,144,145):
  print('sixth coefficient and a,N,j',b,c,*best(6,c,b),flush=True)
 for k in list(range(7,33))+[36,40,48,56,64,72,80,96,112,120,127]:
  print('exact order and a,N,j',b,k,*best(k,poly(128)[k],b),flush=True)
 print('half 128 and a,N,j',b,128,*best(128,F(poly(128)[128],2),b),flush=True)

if __name__=='__main__':
 for n in NS:anchor(n)
 for b in (b0,b2):show(b,0,True)
