#!/usr/bin/python3.10
"""Exact prime counts and real-endpoint check. Run in submission directory."""
from math import isqrt
from functools import lru_cache
from verify import I
from decimal import Decimal as D
from bisect import bisect_right
N=38358837682
m=isqrt(N)+1
s=bytearray(b'\1')*(m+1);s[:2]=b'\0\0'
for p in range(2,isqrt(m)+1):
 if s[p]:s[p*p:m+1:p]=b'\0'*((m-p*p)//p+1)
ps=[p for p in range(m+1) if s[p]]
M=2*3*5*7*11*13
w=[0]
for i in range(1,M+1):
 w.append(w[-1]+int(all(i%p for p in ps[:6])))
def cube(n):
 lo,hi=0,1
 while hi**3<=n:hi*=2
 while hi-lo>1:
  a=(hi+lo)//2
  if a**3<=n:lo=a
  else:hi=a
 return lo
@lru_cache(maxsize=200000)
def phi(x,a):
 if a==0:return x
 if not x:return 0
 if a==6:return (x//M)*w[M]+w[x%M]
 if x<ps[a-1]:return 1
 if x<=m and x<ps[a]**2:return max(0,bisect_right(ps,x)-a)+1
 return phi(x,a-1)-phi(x//ps[a-1],a-1)
@lru_cache(maxsize=None)
def P(x):
 if x<=m:return bisect_right(ps,x)
 a,b,c=map(P,(isqrt(isqrt(x)),isqrt(x),cube(x)))
 t=phi(x,a)+a-1
 for i in range(a,b):
  y=x//ps[i]
  t-=P(y)-i
  if i<c:
   for j in range(i,P(isqrt(y))):t-=P(y//ps[j])-j
 return t
e=I(1).exp()
X=I(N,N+1)
Y=X/e
low=int(Y.a);high=int(Y.b)
assert high<=low+1
assert low==high==14111427770
assert P(N)==P(N+1)==1644673232 and P(low)==632207037
def point(off):
 x=I(D(N)+D(off))
 return e*x/x.ln()*P(low)-P(N)**2
l,r=0,10**8
while r-l>1:
 i=(l+r)//2
 j=point(D(i)/10**8)
 if j.b<0:l=i
 else:
  assert j.a>0
  r=i
a,b=D(l)/10**8,D(r)/10**8
assert point(a).b<0<point(b).a
print('pi(N), pi(N+1), pi(floor(N/e)):',P(N),P(N+1),P(low))
print('N, sign at N:',N,point('0'))
print('root offsets',a,b,point(a),point(b))
