"""Mertens connected comparisons and complete finite coverage."""
from spectral import b0,b2,profile,metc,ceil,cutoffs,pieces,zw,choose,H
from dyad import I,F,exp,PI
from functools import lru_cache
a=F('1.048e-12')
def A(L):return a+I('113.67')*exp(-L/2)
def B(L):return I('1.000100294')*exp(-L/2)+I('2.67')*exp(-2*L/3)
@lru_cache(None)
def T(v,b):
 # Signed damping of the high modes in integral S_Lambda(t)/t^2:
 # the caller divides this bound by v^2.
 t=I(v);d=1-b
 q=choose(sum(y*(1+1/(d+r))/(d+r) for r,y in pieces(v,b,k,j)) for k,j in cutoffs)
 return exp(-d*t)*(2*zw(v,b)/H+q)

def hybrids(L,V,b):
 # Used for 10<=L<=V, any V>=100. These are upper bounds for
 # D2, L*D1 and L*Z (common for the latter two).
 t=I(L)
 s=A(t); c=B(t)
 return s+c, s*(2-t/V)+t/V**2*T(V,b)+c

def testexp(V,b,c,alpha=None):
 # [58,V] join: constant part increases after scaling, separate exponentials
 # on [58,100] (decay faster). [100,V] split once more if needed.
 d=1-b if alpha is None else F(alpha)
 # From [10,29.9], use this gross bound analytically: 2.1 e^-L/2
 # on each side, tail (inc. beyond 58) <= E29.
 v=I('29.9');t=I(10);P=I('2.1e-10')
 E29=2*(v*v+4*v+8)*exp(-v/2)/(8*PI)+P
 C=(I('2.1')*(3+2/t)*exp(-t/2)+2/(exp(t)-1))*exp(d*t)
 D=E29*(1+1/v)*exp(d*v)
 # only used for D02 generous connected rows
 if d==1-b2:
  assert (C+D).below(F(c)*F('.99'))
  assert ((I('2.1')*(3+2/t)*exp(-t/2)/t+E29*(1+1/v)/v+2/(t*(exp(t)-1)))).below('.01')
 # [29.9,58]: theta bound and fixed T58, with L*w(L)<=1+1/v.
 # Direct evaluation after scaling of polynomials in L times e^-(1/2-d)L
 # decreasing from v; constant tail increasing.
 theta0=v*v*exp(-(F(1,2)-d)*v)/(8*PI)
 integ=2*(v*v+4*v+8)*exp(-(F(1,2)-d)*v)/(8*PI)
 Y=theta0+(1+1/v)*(integ+exp(d*58)*P)+2*exp(d*v)/(exp(v)-1)
 assert (Y/(1-Y*exp(-d*v)/v)).below(c)
 # [58,100]: weighted CH2 full plateau transfer, include exponential slack.
 t=I(58)
 Y=2*a*exp(d*100)+I('227.34')*exp(-(F(1,2)-d)*t)+B(t)*exp(d*t)
 assert Y.below(F(c)*F('.999999'))
 # [100,V]: constant part of hybrid increases on normalization by e^{dL}:
 # d*(2-L/V)-1/V>0. exponential parts decrease.
 t=I(100);v=I(V)
 assert d>1/V
 M=(a+T(V,b)/V)*exp(d*v)+I('227.34')*exp(-(F(1,2)-d)*t)+B(t)*exp(d*t)
 assert M.below(F(c)*F('.999999'))
 # e^Y-1 conversion factor <=1.000001 on [29.9,V].
 assert (I(c)*exp(-d*I(58))/I(58)).below('.000001')
 p,q=metc(V,b)
 fac=exp((d-(1-b))*I(V))
 assert d<=1-b and (fac*p).below(c) and (fac*q).below(c)
 if d==F(1,8):
  assert exp(14).above(1198583) and exp(17).above(18002111)
  for l,r,C in [(14,17,F('.28')),(17,F('29.9'),F('.10'))]:
   for v in (l,r):
    assert (C*exp(d*I(v))/I(v)**2).below(c)
 print('connected exponential, b,V,c,slope',b,V,c,d,flush=True)

def powjoin(V,b,m,c,L0=58):
 # Ray on L>=58; envelopes c/L^m (D2) and c/L^(m+1) (other three).
 d=1-b
 t=I(L0); u=I(100);v=I(V)
 assert V>=100 and V>m/d and t.above(2*m)
 assert F(L0)<=100
 for l,r in [(F(L0),61),(max(F(L0),61),70),(max(F(L0),70),100)]:
  if l>r:continue
  e=I(l);g=I(r)
  M=2*a*g**m+(I('227.34')*exp(-e/2)+B(e))*e**m
  assert M.below(F(c)*F('.999999')),(L0,m,c,str(M))
 M=(a+T(V,b)/V)*v**m+(I('227.34')*exp(-u/2)+B(u))*u**m
 assert M.below(F(c)*F('.999999'))
 p,q=metc(V,b)
 scale=exp(-d*v)*v**m
 assert (p*scale).below(c) and (q*scale).below(c)
 assert (I(c)/t**(m+1)).below('.000001')
 print('connected inverse-log, b,V,m,c',b,V,m,c,'from',L0,flush=True)

def small(c):
 # Earlier D02 connected onset: all prime gaps through 22030. Use
 # floor/ceiling constants at D01's independently checked scale.
 from cert import I as C, ln as log, exp as e
 D=2**56
 gamma=C(F(41592772053791273,D),F(41592772053807781,D))
 M=C(F(18842860003214242,D),F(18842860006316737,D))
 B3=C(F(96022672629731889,D),F(96022672663712372,D))
 N=22030
 assert e(10).below(N)
 sieve=bytearray(N+1)
 for i in range(2,N+1):
  if not sieve[i] and i*i<=N:
   sieve[i*i:N+1:i]=b'\1'*(1+(N-i*i)//i)
 ps=[i for i in range(2,N+1) if not sieve[i]]+[N]
 l=log(2);s=h=z=C(0);last=[0]*4
 for p,q in zip(ps,ps[1:]):
  s+=C(F(1,p));h+=l/p;z+=log(C(F(p,p-1)))
  u=log(q)
  R=C(l.a,u.b,True)
  r=z-gamma-log(R)
  # D1,D2,normalized raw product,normalized reciprocal product
  coeff=e(F(5,32)*u);sc=u*coeff
  vals=((s-M-log(R))*sc,(h+B3-R)*coeff,(e(-r)-1)*sc,(e(r)-1)*sc)
  for i,v in enumerate(vals):
   if not v.below(c) or not v.above(-F(c)):last[i]=q
  l=u
 print('small exhaustive, c and starts D1,D2,P,Q',c,*last,flush=True)
 return last

def roots(c,last):
 from cert import I as C, ln as log, exp as e
 D=2**56;d=F(5,32)
 gamma=C(F(41592772053791273,D),F(41592772053807781,D))
 M=C(F(18842860003214242,D),F(18842860006316737,D))
 B3=C(F(96022672629731889,D),F(96022672663712372,D))
 from math import isqrt
 from bisect import bisect_left
 ps=[n for n in range(2,max(last)+1) if all(n%q for q in range(2,isqrt(n)+1))]
 for i,n in enumerate(last):
  j=bisect_left(ps,n);assert ps[j]==n
  p=ps[j-1];zs=ps[:j]
  s=sum((C(F(1,q)) for q in zs),C(0))
  h=sum((log(q)/q for q in zs),C(0))+B3
  z=sum((log(C(F(q,q-1))) for q in zs),C(0))-gamma
  aq=e(z);ap=e(-z)
  t=log(C(p,n))
  def E(x):
   t=log(x);scale=e(d*t)
   return ((s-M-log(t))*t*scale,(h-t)*scale,(1-ap*t)*t*scale,(aq-t)*scale)[i]
  deriv=((1+d*t)*(s-M-log(t))-1,d*(h-t)-1,
         (1+d*t)-(2+d*t)*ap*t,d*(aq-t)-1)[i]
  assert deriv.below(0)
  assert E(p).above(c) and E(n).below(c) and E(n).above(-F(c))
  l=p*10000;u=n*10000
  while u-l>1:
   m=(l+u)//2
   y=E(F(m,10000))
   if y.above(c):l=m
   else:
    assert y.below(c)
    u=m
  assert E(F(l,10000)).above(c) and E(F(u,10000)).below(c)
  print('root D1,D2,P,Q index; bracket x units 10000;',i,l,u,'unique in',p,n,flush=True)

def dominance():
 # Same original exponent, strictly improved matched coefficients.
 for a0,c in [(170,'.00145'),(175,'.00120'),(180,'.00100'),(190,'.00070'),(200,'.00049'),
                 (250,'.000090'),(300,'.000018'),(500,'.000000030')]:
  p,q=metc(a0,b2)
  fac=exp(-I(a0)/32)
  assert (p*fac).below(c) and (q*fac).below(c)
  print('same old exponent 1/8: onset coefficient',a0,c,flush=True)
 # Fix coefficient with no logs, tail (without finite joins) and obtain earlier starts.
 for b,target in [(b2,'.29'),(b2,'.25'),(b2,'.2'),(b2,'.175'),(b2,'.15'),(b2,'.147')]:
  lo=100;hi=100000
  def ok(v):return all(p.below(target) for p in metc(v,b))
  assert ok(hi)
  while lo<hi:
   m=(lo+hi)//2
   if ok(m):hi=m
   else:lo=m+1
  print('fast exponent target, onset',target,lo,flush=True)

if __name__=='__main__':
 testexp(F('168.7136'),b2,'.29446')
 testexp(F('188.92'),b0,'.01890')
 testexp(F('168.7136'),b2,'.0083',alpha=F(1,8))
 for V,b,m,c,L in [('168.7136',b2,3,'.0000051',61),('168.7136',b2,4,'.000851','57.6'),
                   ('168.7136',b2,5,'.144',55),('168.7136',b2,6,'24.3',52),
                   ('188.92',b0,4,'.00134','57.6'),('188.92',b0,5,'.253',55),
                   ('188.92',b0,6,'48',52)]:
  powjoin(F(V),b,m,c,L)
 roots('.29446',small('.29446'))
 dominance()
