#!/usr/bin/python3.10
"""Quantitative real gap immediately after the exact D01 root."""
from math import isqrt
from verify import I,F,D,log,exp0
n=38358837682
b=14111427770
pc=1644673232;qc=632207037
N=10000
L=log(n+1)
e=exp0(1)
assert (e*qc*(L-1)/L**2).above(67000000)
def primes_in(l,r):
 n=isqrt(r)
 occ=bytearray(n+1);s=bytearray(r-l+1)
 for i in range(2,n+1):
  if occ[i]: continue
  if i*i<=n:occ[i*i:n+1:i]=bytes([1])*((n-i*i)//i+1)
  j=max(i*i,((l+i-1)//i)*i)
  if j<=r:s[j-l:r-l+1:i]=bytes([1])*((r-j)//i+1)
 return {i+l for i in range(r-l+1) if not s[i]}
p=primes_in(n+1,n+N)
q=primes_in(b+1,b+N)
old=b
best=None
for m in range(n+1,n+N+1):
 if m in p:pc+=1
 k=I(m)/e
 k0,k1=k.a//D,k.b//D
 assert k0==k1 and old<=k0<=b+N
 for j in range(old+1,k0+1):
  if j in q:qc+=1
 old=k0
 ml=log(m)
 gap=e*m*qc/ml-pc*pc
 # divide by right endpoint squared, multiply by left log^6:
 G=gap*ml**6/(m+1)**2
 assert G.above('0.000007')
 best=G if best is None or G.a<best.a else best
print('Certified strict .000007 on [38358837683,38358847682], lower cell endpoint cap',best.fmt())
