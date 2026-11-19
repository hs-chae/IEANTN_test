#!/usr/bin/python3.10
"""Directed decimal interval arithmetic. See candidate.md for the enclosure proof."""
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from math import factorial, comb
from fractions import Fraction as Q
import json
from os import getenv
RAM_ONLY=getenv("RAM_ONLY")=="1"
F=Context(prec=40,rounding=ROUND_FLOOR)
C=Context(prec=40,rounding=ROUND_CEILING)
N=Context(prec=40)
class I:
 def __init__(self,x=0,y=None):
  if isinstance(x,I): self.a,self.b=x.a,x.b;return
  self.a=D(x);self.b=D(y) if y is not None else self.a
 def __add__(x,y):
  y=I(y);return I(F.add(x.a,y.a),C.add(x.b,y.b))
 __radd__=__add__
 def __neg__(x):return I(x.b.copy_negate(),x.a.copy_negate())
 def __sub__(x,y):return x+-I(y)
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  y=I(y);z=[(a,b) for a in (x.a,x.b) for b in (y.a,y.b)]
  return I(min(F.multiply(a,b) for a,b in z),max(C.multiply(a,b) for a,b in z))
 __rmul__=__mul__
 def inv(x):
  assert x.a>0 or x.b<0
  return I(F.divide(D(1),x.b),C.divide(D(1),x.a))
 def __truediv__(x,y):return x*I(y).inv()
 def __rtruediv__(x,y):return I(y)*x.inv()
 def __pow__(x,n):
  assert isinstance(n,int)
  if n<0:return x.inv()**(-n)
  z=I(1)
  while n:
   if n%2:z=z*x
   n//=2
   if n:x=x*x
  return z
 def exp(x):
  return I(N.next_minus(N.exp(x.a)),N.next_plus(N.exp(x.b)))
 def ln(x):
  assert x.a>0
  return I(N.next_minus(N.ln(x.a)),N.next_plus(N.ln(x.b)))
 def __repr__(x):return f'[{x.a},{x.b}]'
def mn(*z):return I(min(x.a for x in z),min(x.b for x in z))
def pos(x):return I(max(x.a,D(0)),max(x.b,D(0)))
def ex(x):return I(x).exp()
def f(q):return I(q.numerator)/q.denominator if isinstance(q,Q) else I(q)
def E(u,a):return ex(-f(a)*u)
H=3*10**12
h=I(H).ln()
ct={700:'5',750:'6.3',800:'8.2',810:'8.6',820:'9',830:'9.4',840:'9.8',850:'10.2',860:'10.7',870:'11.1'}
@lru_cache(None)
def dens(s):
 c=I(ct[max(i for i in ct if Q(i,1000)<=s)])
 p=(1-s)*Q(8,3);q=5-2*s;d=1-p
 assert (f(d)-f(q)/h).a>0
 x=Q(1)
 pol=I(0)
 for j in range(5):
  if j:x*=q-j+1
  pol+=f(x)/(h**j*f(d)**(j+1))
 v=ex(f(q)*h.ln()-f(d)*h)*pol
 w=(h*h+2*h+2)/H
 ram=I('4.9')*ex(f(p)*I(3).ln())
 r=ram*v+I('51.5')*w
 return 2*(r if RAM_ONLY else mn(c*v+5*w,r))
BETA=[Q(7,8),Q(27,32)]
@lru_cache(None)
def grid(b,s0):
 g=[Q(s,1000) for s in range(s0,int(1000*b)+1)]
 if g[-1]<b:g.append(b)
 w=[]
 for s in g[:-1]:
  z=dens(s)
  w.append(w[-1] if w and w[-1].b<z.a else z)
 w.append(I(0))
 diff=[I(0) if x is y else x-y for x,y in zip(w,w[1:])]
 assert all(z.a>=0 for z in diff)
 return g,diff,w[0]
def XY(u):
 S=(u/2-I('1.83'))**2/I('12.56')+I('.933')
 J=S-I('.933')-I('26.88')**2/I('12.56')+I('1.865')
 return (I('12.546')*u+2*S)*E(u,Q(1,2)),J
def pp(u):return I('1.000000147')*E(u,Q(1,2))+I('1.78')*E(u,Q(2,3))
def ch(u):return I('1.0472e-12')+I('113.67')*E(u,Q(1,2))
def rh(u):return I('.04')*u*u*E(u,Q(1,2))
PIVAL=I('3.14159265358979323846264338327950288','3.14159265358979323846264338327950289')
def chopt(a,b):
 u=I(a,b)
 # T depends pointwise on u; capped before the original RH height.
 T=mn(E(u,Q(-1,2))/2,I(3000175332800))
 v=(T/(2*PIVAL)).ln()
 return PIVAL/(T-1)+PIVAL**2/(3*T**2)+(v*v/(2*PIVAL)-v/(6*PIVAL))*E(u,Q(1,2))
def D02(u):return u*u*E(u,Q(5,32))/64
@lru_cache(None)
def zp(a,b,idx,s0=745,mode='psi'):
 u=I(a,b);g,w,w0=grid(BETA[idx],s0)
 val=sum((c*E(u,1-s) for s,c in zip(g[1:],w)),I(0))
 if mode=='zeros':return val
 e,J=XY(u)
 return e+pos(J-w0)*E(u,1-g[0])+val
@lru_cache(None)
def btheta(a,b,idx):
 u=I(a,b);ls=[ch(u)+pp(u)]
 if a>D('6.4') and b<=D('58.33'):ls.append(rh(u))
 if a>=34:ls.append(chopt(a,b)+pp(u))
 if a>=60:ls.append(zp(a,b,idx)+pp(u))
 if idx and a>=200:ls.append(D02(u)+pp(u))
 return mn(*ls)
def early(u):
 return I('.08')*u*E(u,Q(1,2))+1255*u*E(u,1)
def prefix(u,v):
 # u-v=d; avoid interval cancellation in exp(-d).
 return u*(I('1.0472e-12')*(4*ex(v-u)/v**2+I('1.45')*ex(v/2-u))
            +117*(8*ex(v/2-u)/v**2+I('1.45')*ex(v/4-u))
            +3*E(u,1))
@lru_cache(None)
def e_pi(lo,hi,idx):
 u=I(lo,hi)
 if hi<=D('58.33'):
  old=rh(u)+early(u)
  v=u-8
  ans=btheta(lo,hi,idx)+I('.08')*u*ex(v/2-u)+1255*u*E(u,1)
  for j in range(8):
   w=E(I(j),1)-E(I(j+1),1)
   ans+=u/(u-(j+1))**2*w*btheta(lo-j-1,hi-j,idx)
  return mn(old,ans)
 v=u-16
 pre=prefix(u,v)
 if hi-16<=D('58.33'):
  pre=mn(pre,I('.08')*u*ex(v/2-u)+1255*u*E(u,1))
 ans=btheta(lo,hi,idx)+pre
 for j in range(16):
  w=E(I(j),1)-E(I(j+1),1)
  ans+=u/(u-(j+1))**2*w*btheta(lo-j-1,hi-j,idx)
 return ans
m=12
aa=[factorial(k) for k in range(m+1)]
bs=[sum(aa[j]*aa[k-j] for j in range(m+1) if 0<=k-j<=m) for k in range(2*m+1)]
cs=[sum(aa[j]*comb(k,j) for j in range(k+1))-bs[k] for k in range(m+1)]
assert cs[:5]==[0,0,0,0,1] and all(x>0 for x in cs[4:])
def A(u):return sum((ak/u**k for k,ak in enumerate(aa)),I(0))
def rem(u):
 return factorial(m+1)*(u*E(u,Q(1,2))/10**(m+2) +
          1/(u**(m+1)*(1-2*(m+2)/u)))
def poly(u,order):return sum((cs[k]/u**(k-4) for k in range(4,5+order)),I(0))
@lru_cache(None)
def normerr(lo,hi,idx):
 u=I(lo,hi); v=u-1
 pup=e_pi(lo,hi,idx); pdn=e_pi(lo-1,hi-1,idx)
 if hi<=D('39.47'):pup=mn(pup,3*u*E(u,1))
 if lo>=120:pup=mn(pup,tail_pi_end(u,idx))
 if lo-1>=120:pdn=mn(pdn,tail_pi_end(v,idx))
 eu=pup+2500*u*E(u,1)+rem(u)
 el=pdn+2500*v*E(v,1)
 return u**4*(eu*(2*A(u)+eu)+u/v*el)
def gap(lo,hi,idx,order=-1):
 u=I(lo,hi)
 ls=sum((cs[k]/u**(k-4) for k in range(5+order,m+1)),I(0))
 ls-=sum((bs[k]/u**(k-4) for k in range(m+1,2*m+1)),I(0))
 return ls-normerr(lo,hi,idx)
def tail_pi_end(u,idx,s0=745):
 g,w,w0=grid(BETA[idx],s0)
 b=(I('.04')*u*u+13*u+2)*E(u,Q(1,2))+pp(u)+u*u/50*E(u,1-g[0])
 b+=sum((c*E(u,1-s) for s,c in zip(g[1:],w)),I(0))
 return b*(1+12/u)+prefix(u,u/2)
def tail_err(u,idx):
 u=I(u);v=u-1
 eu=tail_pi_end(u,idx)+2500*u*E(u,1)+rem(u)
 el=tail_pi_end(v,idx)+2500*v*E(v,1)
 return u**4*(eu*(2*A(u)+eu)+u/v*el)
def tail_prove(start,idx,order=-1,margin='0'):
 u=I(start);assert start>=240 and order<=7
 if order==-1:k=0;lead=1-I(margin)
 else:k=order+1;lead=I(cs[4+k])
 loss=sum((bs[j]/u**(j-4) for j in range(m+1,2*m+1)),I(0))+tail_err(u,idx)
 loss=loss*u**k
 assert (lead-loss).a>0, (start,idx,order,lead-loss)
 return str((lead-loss).a)

def aux():
 assert (h-I('28.72')).a>0
 assert (I('58.33').exp()-I('2.169e25')).b<0
 assert I('6.4').exp().a>599
 assert (599/I(2).ln()**2+2/I(2).ln()).b<1255
 u=I(10)
 l=(u.exp()-2)/10
 r=u.exp()/5+I(5).exp()/I(2).ln()
 k=u.exp()*A(u)/u-I(l.a,r.b)
 assert k.a>-2500 and k.b<2500, k
 # elementary pi bracket documented in candidate.md
 assert (I('3.141592653589793239')/H).b<D('1.0472e-12')
 assert (2*I('3.14159')).ln().a>D('1.83')
 assert (2*I('3.14160')).ln().b<D('1.84')
 assert 8*D('3.14159')*D('.04')>1
 assert 2*D('3.14159')>D('6.28')
 assert (1/I(2).ln()).b<D('1.45')
 assert I(34).exp().a>10**9 and (I(17).exp()/2).a>10**7
 assert I('39.47').exp().b<D('1.39e17')
 assert (I(30).exp()/6).a>60 and I(30).exp().a>12
 def ar(n,terms=36):
  return sum((Q((-1)**k,(2*k+1)*n**(2*k+1)) for k in range(terms)),Q(0))
 pil=16*ar(5)-4*ar(239,37)
 pih=16*ar(5,37)-4*ar(239)
 assert Q(PIVAL.a)<pil<pih<Q(PIVAL.b)

if __name__=='__main__':
 import sys
 aux()
 if len(sys.argv)>1 and sys.argv[1]=='probe':
  for u in map(D,sys.argv[2:]):
   print(u,*[str(gap(u,u,j).a)[:13] for j in [0,1]],*[str(gap(u,u,j,2).a)[:13] for j in [0,1]])
