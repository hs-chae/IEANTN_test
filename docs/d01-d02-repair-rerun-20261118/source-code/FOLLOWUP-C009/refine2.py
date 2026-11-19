"""Intervals for the exact-integral limiting coefficients."""
from spectral import rs,aq,h,I,F,exp,ln,b0,b2,ceil,floor,cap,parts
from functools import lru_cache
def B(n,s,c,d):
 al,q=aq(s);y=h;p=I(1);u=p/al
 for j in range(1,n+1):
  p=p*(q-j+1)/(al*y)
  u+=p/al
 return 2*c*exp(q*ln(y)-al*y)*u+2*d*exp(-y)*(y*y+2*y+2)

@lru_cache(None)
def fine_cap(b):
 res=[];cur=None
 for l,u,c,d in parts(b0,F('.001')):
  ends=(b2,u) if l<b2<u else (u,)
  for z in ends:
   A=ceil(B(12,l,c,d),10**12);D=ceil(B(12,z,c,d),10**12)
   assert A>D and (cur is None or A>=cur)
   if cur is None:cur=A
   m=(A-D)/(z-l)
   if cur>D:
    a=z-(cur-D)/m
    if a<b:res.append((a,min(b,z),m))
   if b<=z:return min(cur,A-m*(b-l)),res
   cur=min(cur,D)
   l=z
 raise ValueError(b)

@lru_cache(None)
def new_Z(v,b):
 K,ps=fine_cap(b);t=I(v)
 return K+sum(m*exp((u-b)*t)*(1-exp((l-u)*t))/t for l,u,m in ps)

if __name__=='__main__':
 for b in (b0,b2):
  l,u,c,d=next(t for t in rs if t[0]<=b<t[1])
  hi=B(16,b,c,d)
  lo=B(15,b,c,d)
  for a,z,C,D in rs:
   if z<=l:assert B(3,z,C,D).a>hi.b
  print('exact integral K brackets, b, outward at 1e-12',
      b,floor(lo,10**12),ceil(hi,10**12), 'less than chord',cap(b)[0],flush=True)
  assert hi.below(cap(b)[0])
