#!/usr/bin/python3.10
"""Whole-domain certificates.  No probe result is used as a theorem."""
from verify import *
from mertens import *
# (start, tail join, idx, order of P, next coefficient)
# order -1 means compare to a constant; order>=0 means P_order+d/L^(order+1).
CASES=[
 ('37','240',0,-1,'.1'),('40.5','240',0,-1,'.5'),('42.15','240',0,-1,'.9'),
 ('42.8','240',0,-1,'1'),('47.5','240',0,1,'14'),('48','240',0,1,'19'),
 ('53','240',1,1,'80'),('48','240',1,1,'39'),
 ('217','250',0,2,'0'),('186','245',1,2,'0'),
 ('252','255',0,3,'0'),('210.2','240',1,3,'0'),
 ('287','290',0,4,'0'),('236','245',1,4,'0'),
 ('322','325',0,5,'0'),('262','265',1,5,'0'),
 ('357','361',0,6,'0'),('288','291',1,6,'0'),
 ('394','400',0,7,'0'),('318','320',1,7,'0'),
 ('200','250',0,1,'115'),('200','250',1,2,'1200'),
 ('240','270',0,2,'1300'),('240','270',1,4,'60000')]
def cutoff(lo,hi,check):
 # Adaptive rational subdivisions.  Each successful leaf is an entire-cell proof.
 count=0;worst=None
 def work(a,b,depth):
  nonlocal count,worst
  z=check(a,b)
  if z>0:
   count+=1;worst=z if worst is None else min(worst,z);return
  if a==b or depth==18:raise AssertionError(('cell failure',a,b,z))
  v=(a+b)/2;work(a,v,depth+1);work(v,b,depth+1)
 # Include subinterval boundaries on both sides, with validity by each enclosure.
 lo,hi=D(lo),D(hi)
 p=[lo]+[z for z in map(D,['39.47','58.33','59.33','60','61','74.33','75.33','120','121','200','201'])
          if lo<z<hi]+[hi]
 for a,b in zip(p,p[1:]):work(a,b,0)
 return count, str(worst)
def tail_case(at,idx,k,d):
 u=I(at);assert at>=240
 if k==-1 and D(d)==1:n=1;lead=I(14)
 elif k==-1:n=0;lead=1-I(d)
 else:n=k+1;lead=I(cs[4+n])-I(d)
 loss=u**n*(tail_err(u,idx)+sum((bs[j]/u**(j-4) for j in range(m+1,2*m+1)),I(0)))
 assert (lead-loss).a>0, (at,idx,k,d,lead-loss)
 return str((lead-loss).a)
def rcheck():
 aux()
 for a,b,idx,k,d in CASES:
  check=lambda u,v:(gap(u,v,idx,k)-I(d)/(I(u,v)**(k+1))).a
  fin=cutoff(a,b,check) if a!=b else None
  print('R ray',a,idx,k,d,'join',b, fin,tail_case(int(b),idx,k,d),flush=True)
 for a,b,k,d in [('36.9','37',-1,'0'),('53','125',2,'0'),('58','91',3,'0'),('65','71',4,'0')]:
  print('R bounded',a,b,k,cutoff(a,b,lambda u,v:(gap(u,v,0,k)-I(d)/I(u,v)**(k+1)).a),flush=True)

# polynomial upper joins for prime reciprocal / products (same bound) and weighted prime sum
def mpoly():
 t=I(10**7);v=(t/(2*PIVAL)).ln()
 assert (PIVAL/(t-1)).b<D('3.142e-7')
 assert (v*v/(2*PIVAL)-v/(6*PIVAL)).b<33 and I('27.6').exp().a>10**9
 for start,j,Cc in [('16.7',1,'.15'),('16.45',1,'.16'),('16.25',1,'.18'),('16.05',1,'.19'),
                      ('15.5',0,'.27'),('15.65',0,'.24'),('16',0,'.21'),('16.5',0,'.18'),('18.15',1,'.08'),('18',0,'.079'),('20',1,'.04'),('20',0,'.04')]:
  def check(lo,hi):
   z,r=origpoly(lo,hi,j)
   if j:z=z*r.exp()
   return (I(Cc)-z).a
  a=D(start);b=D('27.6')
  fin1=cutoff(a,b,check)
  fin2=cutoff(b,D(200),check)
  z=sig(D(200),D(200),0,j)+rp(j,I(200))
  # Ignore the subtraction in rp in this monotone tail calculation.
  z+=pp_lower(I(200))
  loss=z*I(200)**2
  if j:loss*= (z/200).exp()
  assert (I(Cc)-loss).a>0
  print('M poly',start,j,Cc,fin1,fin2,str(loss.b),flush=True)
def mpure():
 rows=[(0,180,'.025'),(0,190,'.0161'),(0,200,'.0135'),(0,210,'.0126'),
               (0,220,'.012'),(0,250,'.0111'),(0,300,'.0101'),(0,400,'.0091'),
               (1,160,'.431'),(1,170,'.302'),(1,180,'.258'),(1,185,'.247'),
               (1,190,'.238'),(1,200,'.226'),(1,210,'.217'),(1,220,'.210'),
               (1,250,'.193'),(1,300,'.176'),(1,400,'.159')]
 # Conservative legacy rows; refine.py proves the original exact rows.
 d0={180:'.036',190:'.019',200:'.0142',210:'.0127',220:'.0121'}
 d1={160:'.595',170:'.346',180:'.270',185:'.254',190:'.242',200:'.228',210:'.218'}
 rows=[(i,L,(d1 if i else d0).get(L,s)) for i,L,s in rows]
 for i,L,s in rows:
  t=I(L);a=1-BETA[i];p=pure(L,i,1);q=pure(L,i,0)
  assert (I(s)-p*(p*E(t,a)/t).exp()).a>0 and (I(s)-q).a>0
  print('M pure',i,L,s,str(p.b),str(q.b),flush=True)
 # Auxiliary historical comparison; original .226 row is certified by refine.py.
 assert (I('.226')*E(I(200),Q(1,32))).b<D('.004')
 for x,y in [('16.7','2e7'),('16.45','2e7'),('16.25','2e7'),('16.05','2e7'),('16.5','2e7')]:
  assert I(x).exp().b<D(y)
 assert I('36.9').exp().b<D('1.15e16')<I(37).exp().a
 for x in ['16.7','16.45','16.25','16.05','15.5','15.65','16','16.5']:
  assert I(x).exp().b<20000000
if __name__=='__main__':
 import sys
 if sys.argv[1:]==['R']:rcheck()
 else:mpoly();mpure()
