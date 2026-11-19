#!/usr/bin/python3.10
"""Sharpened one-sided/terminal Ramanujan enclosures."""
from refine import *
from certify import cutoff
import higher
SIGN=D('43.74')
@lru_cache(None)
def ep(lo,hi,idx,upper):
 u=I(lo,hi)
 if upper and hi<=SIGN:return 3*u*E(u,1)
 old=e_pi(lo,hi,idx)
 if lo>=121:return mn(old,term(u,idx))
 if hi>67:return old
 # One-sided Chebyshev prefix and quarter-unit cells near the early joins.
 N=32 if hi<=D('58.33') else 64
 v=u-D(N)/4
 if upper and hi-D(N)/4<=SIGN:pre=3*u*E(u,1)
 elif hi-D(N)/4<=D('58.33'):
  pre=I('.08')*u*ex(v/2-u)+1255*u*E(u,1)
 else:pre=prefix(u,v)
 z=btheta(lo,hi,idx)+pre
 for k in range(N):
  x=D(k)/4;y=x+D('.25')
  if upper and hi-x<=SIGN:continue
  z+=u*(E(I(x),1)-E(I(y),1))/(u-y)**2*btheta(lo-y,hi-x,idx)
 return mn(old,z)

def term(u,idx):
 # Refined monotone analytic tail, applicable for u>=120.
 assert u.a>=120
 b=(I('.04')*u*u+13*u+2)*E(u,Q('.5'))+pp(u)+u*u/50*E(u,Q('.255'))
 b+=spectral(u,idx,7450,5)*E(u,1-BETA[idx])
 return b*(1+1/(u/3-4))+prefix(u,u/2)
def loss(lo,hi,idx,tail=False):
 u=I(lo,hi);v=u-1
 U=term(u,idx) if tail else ep(lo,hi,idx,True)
 Dn=term(v,idx) if tail else ep(lo-1,hi-1,idx,False)
 eu=U+2500*u*E(u,1)+rem(u);el=Dn+2500*v*E(v,1)
 return u**4*(eu*(2*A(u)+eu)+u/v*el)
def shell(u,order,tail=False):
 return (I(0) if tail else sum((cs[k]/u**(k-4) for k in range(5+order,m+1)),I(0)))-sum((bs[k]/u**(k-4) for k in range(m+1,2*m+1)),I(0))
def Grem(lo,hi,idx,k):
 u=I(lo,hi)
 return shell(u,k)-loss(lo,hi,idx)
def tay(L,idx,k,d):
 u=I(L)
 assert L>=121 and L-1>8*(4+k+1+3)
 n=k+1;lead=I(cs[4+n])-I(d)
 out=lead+(shell(u,k,True)-loss(u.a,u.b,idx,True))*u**n
 return out.a
def high(L,idx,n):
 old=higher.tail_pi_end
 try:
  higher.tail_pi_end=term
  return higher.high(L,idx,n)
 finally:higher.tail_pi_end=old

def checks():
 assert I(SIGN).exp().b<10**19
 for a,b,k,d in [('36.94','37',-1,'.1'),('38','40.5',-1,'.5'),
                 ('39.56','42.15',-1,'.9'),('40.16','42.8',-1,'1'),
                 ('47.45','47.5',1,'14'),('52.3','125',2,'0'),
                 ('57.7','91',3,'0'),('63.8','71.8',4,'0')]:
  print('extension',a,b,k,d,cutoff(a,b,lambda u,v:(Grem(u,v,0,k)-I(d)/I(u,v)**(k+1)).a),flush=True)
 cases=[('48',1,1,'42',240),('53',1,1,'82',240),
        ('200',0,1,'116.6',240),('200',1,2,'1240',240),
        ('240',0,2,'1320',270),('240',1,4,'67000',270),
        ('250',0,3,'0',253),('285',0,4,'0',287),('319',0,5,'0',322),
        ('355',0,6,'0',357),('392',0,7,'0',394),('209.95',1,3,'0',212),('216.55',0,2,'0',219),('185.6',1,2,'0',188),('316',1,7,'0',320)]
 for a,i,k,d,b in cases:
  try:
   tail=tay(b,i,k,d);assert tail>0,tail
   fin=cutoff(a,str(b),lambda u,v:(Grem(u,v,i,k)-I(d)/I(u,v)**(k+1)).a)
   print('ray',a,i,k,d,b,fin,tail,flush=True)
  except AssertionError as e:print('not certified',a,i,k,d,b,e,flush=True)
 for n in [8,9,10,12,15,20]:
  for i in range(2):
   a,b=250,1000
   while a+1<b:
    c=(a+b)//2
    if high(c,i,n)>0:b=c
    else:a=c
   z=high(b,i,n);assert z>0
   print('high',n,i,b,z,flush=True)
if __name__=='__main__':checks()
