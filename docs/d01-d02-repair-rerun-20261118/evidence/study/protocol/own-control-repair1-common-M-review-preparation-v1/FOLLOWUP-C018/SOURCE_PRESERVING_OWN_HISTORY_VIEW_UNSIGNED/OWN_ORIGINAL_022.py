#!/usr/bin/python3.10
"""Certificates and pointwise envelopes for the Mertens family."""
from verify import *
def pp_lower(u):
 return pos(1-mn(I('2.4646')/u,I('15.86')/u**2,I('166.64')/u**3,I('2420.8')/u**4))*E(u,Q(1,2))
def rp(J,u):
 # scaled prime-power tail (full), relative constants from Dusart Cor 4.5, Thm 4.2.
 v=(I('1.000000147')*2*E(u,Q(1,2))+I('1.78')*I('1.5')*E(u,Q(2,3)))
 # theta(sqrt(x)) >= sqrt(x)*(1-2*1.2323/L), for sqrt(x)>=2.
 return v-pp_lower(u)
def rparts(a):
 # list (constant, monomial degree, rate)
 m,n=(220,618) if RAM_ONLY else (106,60)
 return [(I('.04'),2,Q(1,2)),(I(13),1,Q(1,2)),(I(2),0,Q(1,2)),
         (I('.02'),2,Q(255,1000)),(I(m)/16,4,a+Q(16,100)),
         (I(n)/4,2,a+Q(1,2)),(I(n),1,a+Q(1,2)),(I(2*n),0,a+Q(1,2))]
def sig(lo,hi,idx,j):
 # Upper bound for scaled error L^j times |F_j| (before prime powers).
 u=I(lo,hi);a=1-BETA[idx]
 z=zp(lo,hi,idx,mode='zeros')
 return (1+2*(1+I(j)/u)/H)*z+sum((c*u**n*E(u,d)*(1+(1+I(j)/u)/(f(d)-n/u)) for c,n,d in rparts(a)),I(0))
def pure(t,idx,j,theta=True):
 # bound on e^(a*L) L^j times |log error or sum error| for all L>=t
 u=I(t);a=1-BETA[idx]
 g,w,w0=grid(BETA[idx],745)
 z=sum((c*E(u,1-s-a) for s,c in zip(g[1:],w)),I(0))
 ans=(1+2*(1+I(j)/u)/H)*z
 ans+=sum((c*u**n*E(u,d-a)*(1+(1+I(j)/u)/(f(d)-n/u)) for c,n,d in rparts(a)),I(0))
 for c,n,d in rparts(a):assert t*(d-a)>n
 if theta:ans+=(I('2.000000294')*E(u,Q(1,2)-a)+I('2.67')*E(u,Q(2,3)-a))*(1+I(j)/u)
 return ans
def wc(lo,hi,j):
 u=I(lo,hi)
 c=I('1.0472e-12');f=I('3.142e-7');t=I('27.6')
 ch1=mn(ch(u),f+33*E(u,Q(1,2)))
 ch0=(mn(2*c+I('113.67')*E(u,Q(1,2))*(1+2/u),
         2*f+33*E(u,Q(1,2))*(1+2/u)))
 if hi<=D('27.6'):
  pre=I('.8')*E(u,Q(1,2))
  if not j:return pre
  tail=mn(c/t+I('227.34')*E(t,Q(1,2))/t**2,
          f/t+66*E(t,Q(1,2))/t**2)
  return pre*(1+2/u)+u*tail
 return ch0 if j else ch1
def origpoly(lo,hi,j):
 # An entire-cell bound for L^(2+j) times the error.
 u=I(lo,hi)
 z=wc(lo,hi,j)+rp(j,u)
 if lo>=60:z=mn(z,sig(lo,hi,0,j)+rp(j,u))
 return z*u*u, z/u**j
def simple_check():
 assert (I('27.6').exp()).b<10**12+3
 assert (I(30)-I(6).ln()).a>28
 assert (I('.32')-I('3.51')/28).a>D('.19')
 assert (I(6).ln()*I('.32')).exp().b<2
 for i in range(2):
  for L in ([180,190,200,205,210,220,250,300,350,400] if not i else [160,170,175,180,185,190,200,205,210,220,250,300,350,400]):
   print('pure',i,L,*[str(pure(L,i,j).b)[:10] for j in (0,1)])
 for t in ['13.7','14','15','16','17','18','19','20','24','27.6','27.61','28','30','50','100','170','180','190']:
  z=D(t)
  print('poly',z,*[str(origpoly(z,z,j)[0].b)[:10] for j in [0,1]])
if __name__=='__main__':simple_check()
