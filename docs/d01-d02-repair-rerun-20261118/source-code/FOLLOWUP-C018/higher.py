#!/usr/bin/python3.10
"""Further-order all-ray certificates, no joins by sampling."""
from verify import *
def high(t,idx,n):
 # n is the last order kept, i.e. P_n contains 1 through L^{-n}.
 # Include n+1 as positive cushion; truncate pi at m=n+6.
 m=n+6;b=2*m+4;k=n+1
 assert t-1>=max(2*b,120,8*(k+7))
 u=I(t); v=u-1
 aa=[factorial(j) for j in range(m+1)]
 bb=[sum(aa[j]*aa[i-j] for j in range(m+1) if 0<=i-j<=m) for i in range(2*m+1)]
 def ap(u): return sum((a/u**i for i,a in enumerate(aa)),I(0))
 def rr(u):
  return factorial(m+1)*(u*E(u,Q(1,2))/b**(m+2)+
          1/(u**(m+1)*(1-2*(m+2)/u)))
 kap=2*I(b).exp()
 err=tail_pi_end(u,idx)+kap*u*E(u,1)+rr(u)
 erl=tail_pi_end(v,idx)+kap*v*E(v,1)
 loss=(u**4*(err*(2*ap(u)+err)+u/v*erl)+
       sum((bb[j]/u**(j-4) for j in range(m+1,2*m+1)),I(0)))*u**k
 lead=sum(aa[j]*comb(n+5,j) for j in range(n+6))-bb[n+5]
 return (I(lead)-loss).a
if __name__=='__main__':
 for n in [8,9,10,12,15,20]:
  for idx in [0,1]:
   a,b=250,1000; assert high(b,idx,n)>0
   while a+1<b:
    c=(a+b)//2
    if high(c,idx,n)>0:b=c
    else:a=c
   assert high(b,idx,n)>0
   print(n,idx,b,high(b,idx,n))
