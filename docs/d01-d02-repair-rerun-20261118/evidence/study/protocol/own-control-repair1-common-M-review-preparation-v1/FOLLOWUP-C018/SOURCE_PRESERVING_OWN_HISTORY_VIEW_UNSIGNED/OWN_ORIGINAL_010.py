#!/usr/bin/python3.10
"""Application of a continuous cumulative-density majorant and original comparators."""
from verify import *
from mertens import rparts
from pathlib import Path
def sqrt(x):return (x.ln()/2).exp()
def C_r(s):
 p=Q(8,3)*(1-s);q=5-2*s;d=1-p
 return 2*(I('4.9')*ex(f(p)*I(3).ln()+f(q)*h.ln()-f(d)*h)/(f(d)-f(q)/h)
          +I('51.5')*(h*h+2*h+2)/H)
def cont(u,idx,j):
 # Scaled by exp(aL); no prime-power subtraction needed.
 u=I(u);a=1-BETA[idx]
 z=C_r(BETA[idx])*u/(u-105)
 z*=1+2*(1+I(j)/u)/H
 z+=sum((c*u**n*E(u,d-a)*(1+(1+I(j)/u)/(f(d)-n/u)) for c,n,d in rparts(a)),I(0))
 z+=(I('2.000000294')*E(u,Q(1,2)-a)+I('2.67')*E(u,Q(2,3)-a))*(1+I(j)/u)
 return z
def guards():
 # Check against 0.005 exp(-L/8) for relative endpoint radii.
 # For j=1 this is the normalized radius after multiplication by L.
 tab=json.loads(Path(__file__).with_name('source-tables.json').read_text())
 base=I('.005').ln()
 def check_const(L,val):
  assert (I(val).ln()+I(max(L,200))/8-base).a>0,(L,val)
 def check_curve(L,A,B,Cc,R='1'):
  L=max(L,200);x=I(L)/I(R)
  # The log derivative has lower bound 1/8 - C/(2 sqrt(R L)), so applies if B>=0.
  assert D(B)>=0 and (I(1)/8-I(Cc)/(2*sqrt(I(L)*I(R)))).a>0
  assert (I(A).ln()+I(B)*x.ln()-I(Cc)*sqrt(x)+I(L)/8-base).a>0
 def check_poly(L,coef,k):
  L=max(L,200)
  assert L>8*k
  assert (I(coef).ln()-k*I(L).ln()+I(L)/8-base).a>0
 for name in ['FKS-5','Dusart-1']:
  for L,val in tab[name]:check_const(int(L),val)
 for L,v,b,c,k in tab['PT-1']:
  check_const(int(L),k);check_curve(int(L),v,b,c,'5.573412')
 # 0.848 > 2 / sqrt(5.5666305), safe test for FKS Table 6.
 assert (2/sqrt(I('5.5666305'))).b<D('.848')
 # Change the normalization from (L/R)^1.5 to L^1.5.
 for L,v in tab['FKS-6']:check_curve(int(L),str((I(v)/14).a),'1.5','.848')
 assert (I('5.5666305')*sqrt(I('5.5666305'))).b<14
 assert (I('5.573412')*sqrt(I('5.573412'))).b<14
 check_curve(200,'9.22022','1.5','.8476836');check_curve(200,'2','1.5','.8476836')
 check_curve(200,'.18','.25','.394') # PT (18) fallback, weakened in both directions
 check_const(200,'1.047e-12');check_const(1000,'1.94751e-12');check_const(40,'1.93378e-8')
 for c in ['.001','.01','.2','.3','.5','.15','.18']:check_poly(200,c,4)
 assert grid(BETA[0],745)[1][-1].a>D('.005')
 assert (I('.004')-I('.226')*E(I(200),Q(1,32))).a>0
 assert (I('.0135')*E(I(224),Q(1,8))).b < D('1e-14')
 assert (I('.238')*E(I(198),Q(5,32))).b < D('1e-14')
 assert (I('.0111')*E(I(296),Q(1,8))).b < D('1e-18')
 assert (I('.193')*E(I(255),Q(5,32))).b < D('1e-18')
 print('row counts', {k:len(v) for k,v in tab.items()}, 'matched endpoint lower guard .005; D ray wins from 200')
def continuous():
 assert (I('.32')-I('3.51')/h).a>D('.197')
 s=2*h.ln()+f(Q(8,3))*(h+I(3).ln())+(f(Q(8,3))+2/h)/(I('.32')-I('3.51')/h)
 assert s.b<105
 for i,rows in enumerate([{600:'.0082',1000:'.0076',2000:'.0072',4000:'.0070',10000:'.0069'},
                       {600:'.144',1000:'.132',2000:'.125',4000:'.122',10000:'.120'}]):
  print('boundary coefficient',i,C_r(BETA[i]),'Taylor bound',dens(BETA[i]))
  for L,val in rows.items():
   c=cont(L,i,1);d=cont(L,i,0)
   assert (I(val)-c*(c*E(I(L),1-BETA[i])/L).exp()).a>0 and (I(val)-d).a>0
   assert all((L*(rate-1+BETA[i]))>n for _,n,rate in rparts(1-BETA[i]))
   print('continuous',i,L,val,c.b,d.b)
 assert (I('.226')*E(I(200),Q(1,32))).b<D('.002')
 assert (I('.226')/I('.0135')*E(I(200),Q(1,32))).b<D('.033')
 assert (I('.025')*I(180)**2*E(I(180),Q(1,8))).b<D('.2')
 assert (I('.431')*I(160)**2*E(I(160),Q(5,32))).b<D('.2')
 assert (I('1.000000147')*E(I(200),Q(3,8))+I('1.78')*E(I(200),Q(13,24))).b<D('.001')
if __name__=='__main__':aux();guards();continuous()
