from fractions import Fraction as F
from math import isqrt
from certify import ex,E,EP
def pi(n):
 r=isqrt(n)
 v=[n//k for k in range(1,r+1)]
 if v[-1]==r:small=r-1
 else:small=r
 hi=[0]+[q-1 for q in v]; lo=[0]+[k-1 for k in range(1,small+1)]
 def get(y):return lo[y] if y<=small else hi[n//y]
 for p in range(2,r+1):
  if get(p)==get(p-1):continue
  a=get(p-1)
  for i,q in enumerate(v,1):
   if q<p*p:break
   hi[i]-=get(q//p)-a
  for q in range(small,p*p-1,-1):lo[q]-=lo[q//p]-a
 return hi[1]
def lograt(v):
 k=0
 while v>=2: v/=2;k+=1
 def ser(x):
  z=(x-1)/(x+1)
  a=2*sum(z**m/m for m in range(1,120,2))
  return a,a+2*z**121/(1-z*z)
 a,b=ser(v);c,d=ser(F(2))
 return a+k*c,b+k*d
def cmp(x,a,b):
 lo,hi=lograt(x)
 return x*b/(E(1)*hi)-a*a, x*b*EP(1)/lo-a*a
if __name__=='__main__':
 B=38358837682
 u,v=ex(1)
 n=int(B*u)
 assert n<=B*u and (B+1)*v<n+1
 a,b=pi(B),pi(n)
 print(B,n,a,b,flush=True)
 assert cmp(F(B),a,b)[1]<0
 a1=pi(B+1)
 assert cmp(F(B+1),a1,b)[0]>0
 print('pi(B+1)',a1,flush=True)
 lo=F(B);hi=F(B+1)
 # B+1 need not have same pi; the comparison here freezes pi at B.
 if cmp(hi,a,b)[0]<=0:
  print('no interior crossing with frozen prime counts')
 else:
  for j in range(18):
   m=(lo+hi)/2
   p,q=cmp(m,a,b)
   if p>0:hi=m
   elif q<0:lo=m
   else:raise ArithmeticError
  print(lo-B,hi-B,float(lo-B),float(hi-B))
