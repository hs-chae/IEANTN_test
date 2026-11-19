#!/usr/bin/python3.10
"""Refined signed Mertens and continuous spectral certificates."""
from mertens import *
from functools import lru_cache
hh=I(HT).ln()
def powq(u,q):return ex(f(q)*u.ln())
def pars(s):
 p=Q(8,3)*(1-s); q=5-2*s; d=1-p
 A=I('4.9')*powq(I(3),p)
 B=I('51.5')
 if not RAM_ONLY and s>=Q('.70'):
  c=I(ct[max(k for k in ct if Q(k,1000)<=s)])
  if (A-c).a>=0:A=c;B=I(5)
 return A,B,q,d
@lru_cache(None)
def moment(s,ram=False):
 # Minimize only over pairs that are source bounds.
 A,B,q,d=pars(s)
 pol=I(0); x=Q(1)
 for j in range(5):
  if j:x*=q-j+1
  pol+=f(x)/(hh**j*f(d)**(j+1))
 v=E(hh,d)*powq(hh,q)*pol
 w=(hh**2+2*hh+2)/HT
 r=I('4.9')*powq(I(3),1-d)*v+I('51.5')*w
 return 2*(r if ram else mn(A*v+B*w,r))
@lru_cache(None)
def breaks(idx,start,step):
 g=[Q(k,10000) for k in range(start,int(BETA[idx]*10000)+1,step)]
 if g[-1]<BETA[idx]:g.append(BETA[idx])
 return g
@lru_cache(None)
def mesh(idx,start,step):
 g=breaks(idx,start,step); ws=[]
 for s in g[:-1]:
  z=moment(s)
  ws.append(ws[-1] if ws and ws[-1].b<=z.a else z)
 ws.append(I(0))
 diff=[I(0) if x is y else x-y for x,y in zip(ws,ws[1:])]
 assert all(z.a>=0 for z in diff)
 return g,diff
def spectral(u,idx,start,step):
 a=1-BETA[idx];g,w=mesh(idx,start,step)
 return sum((c*E(u,1-s-a) for s,c in zip(g[1:],w)),I(0))
@lru_cache(None)
def parts(idx,start):
 a=1-BETA[idx];s=Q(start,10000)
 terms=[(I('.04'),Q(2),Q('.5'),None),(I(13),Q(1),Q('.5'),None),
        (I(2),Q(0),Q('.5'),None),(I('.02'),Q(2),1-s,None)]
 # Bounding cumulative counts on the tail above T before real-part integration.
 g=breaks(idx,start,100)
 # Telescoping real-part integral is bounded above by a sum of positive bands
 # (drop the subtraction here; tail is already very small).
 for s,t in zip(g,g[1:]):
  A,B,q,d=pars(s)
  terms.append((2*A*powq(I(6),d)/powq(I(2),q),q,1-t+d/2,(d,q)))
  for j,c in [(2,3*B),(1,12*B),(0,24*B)]:
   terms.append((c,Q(j),Q('.5')+1-t,None))
 return terms
def residual(u,idx,j,start):
 a=1-BETA[idx]
 ans=I(0)
 for c,n,d,de in parts(idx,start):
  assert (f(d-a)*u-f(n)).a>0
  if de:
   dd,q=de
   den=f(dd)-f(q)/(u/2-I(6).ln());assert den.a>0
   c=c/den
  ans+=c*powq(u,n)*E(u,d-a)*(1+(1+I(j)/u)/(f(d)-f(n)/u))
 return ans

def slope(s):
 # Bound negative logarithmic derivative for the Ramaré Taylor majorant.
 d=1-Q(8,3)*(1-s); q=5-2*s
 v=f(q)/(hh*f(d))
 return f(Q(8,3))*(hh+I(3).ln())+2*hh.ln()+f(Q(8,3))/f(d)+(f(Q(8,3))/f(d)+8)*v/(1-v)

def rad(t,idx,j,start=7200,step=5,continuous=False,with_tail=True):
 # e^(aL) L^j-scaled full prime-sum and log radius, evaluated at t.
 u=I(t);a=1-BETA[idx]
 assert u.a>=130
 if continuous:
  assert u.a>105 and start==7450 and slope(Q('.745')).b<105
  z=moment(BETA[idx],ram=True)*u/(u-105)
 else:z=spectral(u,idx,start,step)
 # The exact series gives the sharper factor 1+j/(aL)
 # by parts, but the original 1+2(1+j/L)/H is stronger at practical L.
 z*=mn(1+2*(1+I(j)/u)/HT,1+I(j)/(f(a)*u))
 z+=residual(u,idx,j,start)
 if with_tail:z+=I('2.000000294')*E(u,Q('.5')-a)+I('2.67')*E(u,Q(2,3)-a)
 return z
def common(t,idx,start=7200,step=5,continuous=False):
 p=rad(t,idx,1,start,step,continuous)
 return I(0,max(rad(t,idx,0,start,step,continuous).b,(p*(p*E(I(t),1-BETA[idx])/I(t)).exp()).b))

ORIG=[[(180,'.025'),(190,'.0161'),(200,'.0135'),(210,'.0126'),(220,'.012'),
       (250,'.0111'),(300,'.0101'),(400,'.0091')],
      [(160,'.431'),(170,'.302'),(180,'.258'),(185,'.247'),(190,'.238'),(200,'.226'),(210,'.217'),(220,'.210'),
       (250,'.193'),(300,'.176'),(400,'.159')]]
NEW=[[(150,'.01751'),(160,'.01593'),(170,'.01476'),(180,'.01386'),(190,'.01314'),
      (200,'.01256'),(210,'.01207'),(220,'.01166'),(250,'.01075'),(300,'.00981'),(400,'.00884')],
     [(130,'.416'),(140,'.353'),(150,'.311'),(160,'.282'),(169,'.263'),(170,'.261'),(180,'.245'),(185,'.238'),(190,'.232'),
      (200,'.221'),(210,'.213'),(220,'.205'),(250,'.189'),(300,'.172'),(400,'.155')]]
CONT=[['.00808','.00745','.00704','.00685','.006735'],['.141','.130','.123','.120','.1175']]
def certify_refine():
 from certify import cutoff
 from comparison import guards
 aux()
 assert I(65).exp().a/6>HT
 assert (hh-I('28.72')).a>0
 # FKS Lemma 5.2 domain repair; on [.85,1] exactly one prime power is present.
 assert I('.85').exp().a>2 and I(1).exp().b<3
 assert (I('.8476836')**2*4).b<9
 def fks(u):
  return 2*powq(u,Q(3,2))*E(powq(u,Q(1,2)),Q('.8476836'))
 assert min(fks(I(1)).a,fks(I(40)).a)>D('.77')
 assert (I('.8476836')**2*40).a>9
 assert fks(I(1000)).a>D('1.93378e-8') and fks(I(2100)).a>D('1.94751e-12')
 print('FKS small-domain repair',cutoff('.85','1',lambda lo,hi:(fks(I(lo,hi))-1+I(2).ln()*E(I(lo,hi),1)).a))
 # Both the historical statements and the tighter refined rows are tested.
 for name,rows in [('restored',ORIG),('refined',NEW)]:
  for i,row in enumerate(rows):
   for t,v in row:
    z=common(t,i);assert z.b<D(v)
    print(name,i,t,v,z.b)
 for i,row in enumerate(CONT):
  for t,v in zip([600,1000,2000,4000,10000],row):
   z=common(t,i,start=7450,continuous=True);assert z.b<D(v)
   print('continuous',i,t,v,z.b)
 for i,t,v in [(0,'185.8','.01343'),(1,'167.75','.265')]:
  u=I(t);a=1-BETA[i];g=I(v)
  z=common(t,i);assert z.b<g.a
  b=I('113.67')*(1+2/I(50))+I('2.000000294')+I('2.67')
  zz=I('1.0472e-12')*E(u,-a)+g/(f(a)*u)+b*E(I(50),Q('.5')-a)
  assert (f(a)*u).a>1
  # Upper bound for unscaled j=1 radius for 50<=L<=t.
  logcap=(2*I('1.0472e-12')+g*E(u,a)/(f(a)*u)+b*E(I(50),Q('.5')))/50
  assert (zz*logcap.exp()).b<g.a,(i,t,v,zz)
  for lo,hi,c in [('13.7','20','.3'),('20','50','.04')]:
   assert max((I(c)*E(I(w),-a)/I(w)**2).b for w in (lo,hi))<g.a
  assert I('13.7').exp().b<912560
  print('connected',i,t,v,z.b,(zz*logcap.exp()).b)
 for i,t,v in [(0,223,'1e-14'),(1,197,'1e-14'),(0,295,'1e-18'),(1,255,'1e-18')]:
  z=common(t,i)*E(I(t),1-BETA[i]); assert z.b<D(v)
  print('target',i,t,v,z.b)
 guards(169)
 assert mesh(0,7200,5)[1][-1].a>D('.005')
 assert moment(Q(7,8),ram=True).a>D('.005')
 u=I(169); g=I('.263')
 assert common(169,1).b<g.a
 assert (g*E(u,Q(5,32))).b<D('.9')*D('1.047e-12')
 assert (g*E(u,Q(1,32))).b<D('.9')*D('.005')
 assert (u*E(u,Q(1,2))).b<1
 assert pp(u).b<D('.001')*D('1.047e-12')
 assert (pp(u)*E(u,-Q(1,8))).b<D('.001')*D('.005')
 assert (I('.221')/I('.01256')*E(I(200),Q(1,32))).b<D('.035')
 print('strict pointwise guard from log 169')
 polycheck()
 for i in range(2):print('Taylor cap',i,moment(BETA[i],ram=True))
def polycheck():
 from certify import cutoff
 assert I('17.95').exp().a>121
 for t,j,c in [('18.05',1,'.08'),('18.15',1,'.077'),('20',1,'.037'),
               ('17.95',0,'.079'),('18',0,'.0774'),('20',0,'.035')]:
  def check(lo,hi):
   u=I(lo,hi)
   z=wc(lo,hi,j)+I('1.000100294')*E(u,Q('.5'))+I('2.67')*E(u,Q(2,3))
   if lo>=60:z=mn(z,sig(lo,hi,0,j)+I('1.000100294')*E(u,Q('.5'))+I('2.67')*E(u,Q(2,3)))
   return (I(c)-u*u*z*( (z/u).exp() if j else 1)).a
  b=200;a=D(t);k=D('27.6')
  p=cutoff(a,k,check);q=cutoff(k,b,check)
  u=I(200);z=(sig(D(200),D(200),0,j)+I('2.000000294')*E(u,Q('.5'))+I('2.67')*E(u,Q(2,3)))
  loss=z*u*u*((z/u).exp() if j else 1)
  assert loss.b<D(c)
  print('sharper polynomial',t,j,c,p,q,loss.b)
if __name__=='__main__':certify_refine()
