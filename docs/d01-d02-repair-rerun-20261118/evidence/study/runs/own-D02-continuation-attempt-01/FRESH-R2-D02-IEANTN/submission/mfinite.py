#!/usr/bin/python3.10
"""Early exact finite real-cell Mertens extension using validated D01 constants."""
from verify import I,F,log,expb,mini
from pathlib import Path
from math import isqrt
f=Path(__file__).with_name("sieve-results.txt")
c=list(map(int,f.read_text().splitlines()[0].split(": ")[1].split()))
def norm(i):
 return I.raw(I(F(c[i],2**58)).a,I(F(c[i+1],2**58)).b)
ga,mm,ww=(norm(i) for i in (0,2,4))
def mx(*xs):
 return I.raw(max(x.a for x in xs),max(x.b for x in xs))
def up(x,k=10000):
 return -(-(x.b*k)//(1<<384))
bins=[2,10,100,1000,10000,50000,100000]
N=bins[-1]
sieve=bytearray(N+1)
for p in range(2,isqrt(N)+1):
 if not sieve[p]:
  sieve[p*p:N+1:p]=bytes([1])*((N-p*p)//p+1)
pr={p for p in range(2,N+1) if not sieve[p]}
pts=sorted(set(bins)|pr)
A,B,C=I(0),I(0),I(0)
L=log(2);lL=log(L)
maxima=[0]*4
j=0
def scores(l,r,ll,lr,A,B,C):
 # z lower/upper across entire cell, not just samples
 rS=mx(A-ll-mm,lr+mm-A)
 rW=mx(B-l+ww,r-ww-B)
 zu=C-ll-ga; nzl=lr+ga-C
 eP=mx(expb(nzl)-1,1-expb(-zu))
 eQ=mx(expb(zu)-1,1-expb(-nzl))
 return [up(rS*r**3),up(rW*r**2),up(eP*r**3),up(eQ*r**3)]
for a,b in zip(pts,pts[1:]):
 if a in pr:
  A+=I(1)/a
  B+=L/a
  C+=log(I(a)/(a-1))
 R,lR=log(b),None
 lR=log(R)
 maxima=list(map(max,zip(maxima,scores(L,R,lL,lR,A,B,C))))
 if b==bins[j+1]:
  if b in pr:
   # include prime bin endpoint on both closed bins
   maxima=list(map(max,zip(maxima,scores(R,R,lR,lR,A+I(1)/b,B+R/b,C+log(I(b)/(b-1))))))
  print('M finite bin',bins[j],b,maxima,'/10000',flush=True)
  j+=1;maxima=[0]*4
 L,lL=R,lR
assert j==len(bins)-1
