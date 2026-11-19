"""Exact integer directed interval arithmetic and certificates."""
from math import factorial as f, comb, isqrt
from fractions import Fraction as F
BITS=256
S=1<<BITS
class I:
 def __init__(self,x,y=None,raw=False):
  if raw: self.a,self.b=x,y;return
  if isinstance(x,I): self.a,self.b=x.a,x.b;return
  z,w=F(x)*S,F(x if y is None else y)*S
  self.a=z.numerator//z.denominator;self.b=-(-w.numerator//w.denominator)
 def __add__(self,y):
  y=I(y);return I(self.a+y.a,self.b+y.b,True)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a,True)
 def __sub__(self,y):return self+-I(y)
 def __rsub__(self,y):return I(y)+-self
 def __mul__(self,y):
  y=I(y);q=[a*b for a in (self.a,self.b) for b in (y.a,y.b)]
  return I(min(q)//S,-(-max(q)//S),True)
 __rmul__=__mul__
 def __truediv__(self,y):
  y=I(y);assert y.a*y.b>0
  q1=[a*S//b for a in (self.a,self.b) for b in (y.a,y.b)]
  q2=[-(-a*S//b) for a in (self.a,self.b) for b in (y.a,y.b)]
  return I(min(q1),max(q2),True)
 def __rtruediv__(self,y):return I(y)/self
 def __pow__(self,n):
  if n<0:return 1/(self**(-n))
  a=I(1);b=self
  while n:
   if n%2: a=a*b
   b=b*b;n//=2
  return a
 def above(self,x):return F(self.a,S)>F(x)
 def below(self,x):return F(self.b,S)<F(x)
 def __str__(self):return '[%.15g, %.15g]'%(self.a/S,self.b/S)
def exp1(t):
 if t<0:return 1/exp1(-t)
 n=max(1,(t+S-1)//S);t=I(t,t,True)/n
 w=r=I(1)
 for j in range(1,27): w=w*t/j;r=r+w
 return (r+I(0,F(2,f(27))))**n
def exp(t):
 t=I(t);return I(exp1(t.a).a,exp1(t.b).b,True)
def lnunit(t):
 z=(t-1)/(t+1);z2=z*z;w=z;r=w
 for j in range(1,39):w=w*z2;r=r+w/(2*j+1)
 return 2*r+I(0,F(3,3**79))
LN2=lnunit(I(2))
def lnraw(t):
 assert t>0
 k=t.bit_length()-1-BITS
 return k*LN2+lnunit(I(F(t,S)*F(2)**(-k)))
def ln(t):
 t=I(t);return I(lnraw(t.a).a,lnraw(t.b).b,True)
def atan_inv(q):
 return sum((I(F((-1)**k,(2*k+1)*q**(2*k+1))) for k in range(32)),I(0))+I(0,F(1,65*q**65))
PI=16*atan_inv(5)-4*atan_inv(239)
a=I('1.048e-12')
def A(t):return sum(f(j)/t**j for j in range(17))
def U(t):return A(t)+3*f(17)/t**17
def delta(t,plus=False):
 b=(t-2*ln(t/(PI*exp(1))))**2-4
 C=2000+I('.08')*exp(17)/(4*PI)
 return ((b+I('1.84')*t)/(8*PI)+I('-.9999' if plus else '1.01'))*exp(-t/2)+C*t*exp(-t)
def ch(t):
 return a*(1+2/t)+115*(1+3/t)*exp(-t/2)+2000000*t*exp(-t)
def powth(t):return I('1.000000147')*exp(-t/2)+I('1.78')*exp(-2*t/3)
def qe(t):
 return t*t/100*exp(-t/2)+t*t/200*exp(-t/5)+I('.010445')*t/(t-92)*exp(-t/8)+I('2.091')*t*exp(-t/4)
def qr(t):return (1+4/t)*(qe(t)+powth(t))+I('3e-16')*t*exp(100-t)
def err(t,hi=None,plus=False):
 choices=[ch(t)]
 if (t if hi is None else I(hi)).b<=58*S:choices.append(delta(t,plus))
 if t.a>=100*S:choices.append(qr(t))
 return min(choices,key=lambda v:v.b)
co=[sum(f(j)*comb(k,j) for j in range(min(16,k)+1)) for k in range(35)]
p=[f(j) for j in range(17)]+[3*f(17)]
for j,x in enumerate(p):
 for k,y in enumerate(p):co[j+k]-=x*y
assert co[:6]==[0,0,0,0,1,14]
def gl(lo,hi):
 z=I(1/hi,1/lo);ans=I(0)
 for c in co[:3:-1]:ans=c+z*ans
 return ans
def rloss(l,u,oneside=False):
 y=err(I(l-1),u-1);t=I(l);g=I(u)
 v=t/(t-1)*y
 if not oneside:
  z=err(t,u,True);v=v+(2*U(t)+z)*z
 return g**4*v
def density():
 h=ln(3*10**12); b=I(F(7,8)); alpha=(8*b-5)/3; q=5-2*b
 w=I(1);z=1/alpha
 for j in range(1,5):
  w=w*(q-(j-1))/(alpha*h);z+=w/alpha
 B=2*(I('11.076')*exp(q*ln(h)-alpha*h)*z+I('3.694')*exp(-h)*(h*h+2*h+2))
 assert B.below('.010445')
 assert ((8*h/3+2*ln(h))+(I(F(8,3))+2/h)/(I(F(7,15))-I('3.4')/h)).below(92)
 # To handle the small e^-100 term, test the rescaled expression directly:
 t=I(200)
 assert (t*t/100*exp(-3*t/8)+t*t/200*exp(-3*t/40)+I('.010445')*t/(t-92)+I('2.091')*t*exp(-t/8)+I('1.000000147')*exp(-3*t/8)+I('1.78')*exp(-13*t/24)).below('.020')
 assert (exp(17)/(4*PI)+2000).below(2000000)
 for t in (34,58):
  t=I(t);T=2*PI**2*exp(t/2)/t
  assert T.above(10**7) and T.below(3*10**12)
 assert (2*ln(34/(PI*exp(1)))).above('2.7')
 assert (I('1.000000147')+I('1.78')*exp(-I(F(34,6)))).below('1.01')
 r=I(0);w=I(1)
 for j in range(1,201):w=w*35/j;r+=w/j
 ei=I(-1,1)+ln(35)+r+I(0,F(2*35**201,f(201)))
 assert (ei-exp(35)/35*A(I(35))).above(0)
 assert (ei-exp(35)/35*U(I(35))).below(0)
 assert exp(58).below(2169*10**22)
 assert exp(I('39.32')).below(12*10**16)
 assert (a*2/100**2+115*3*exp(-50)/100**2+2000000*exp(-100)).below('3e-16')
 for base,n in [(36,11),(192,11),(201,15),(250,16)]:
  neg=sum((I(F(-co[k],base**(k-n))) for k in range(n+1,35) if co[k]<0),I(0))
  assert (co[n]-neg).above(0),(base,n)
 print('QRH constants / li anchors / polynomial: OK',flush=True)

def grid(start,stop,step,profile,oneside=False):
 l=F(start);stop=F(stop);step=F(step);margin=None
 while l<stop:
  u=min(l+step,stop)
  v=gl(l,u)-rloss(l,u,oneside)-profile(I(l,u))
  assert v.above(0), (l,u,str(v))
  margin=v.a if margin is None else min(margin,v.a);l=u
 print('grid',start,stop,step,oneside,'slack >=',margin/S,flush=True)
def ranu():
 density()
 for start,c in [('36.72','.003'),('36.74','.013'),('36.80','.04'),('37','.13'),('37.5','.34'),('38','.51'),('39','.788')]:
  grid(start,'39.32','.002',lambda t:I(c),True)
 for start,c in [('39.31','.08'),('40','.37'),('41','.68'),('42','.898'),('42.65','1')]:
  grid(start,'59','.003',lambda t:I(c))
 grid('47.25','59','.003',lambda t:1+14/t)
 for start,end,c in [('43','59','1.04'),('44','59','1.14'),('46','59','1.25'),('47.5','56.5','1.30')]:
  grid(start,end,'.004',lambda t:I(c))
 grid('59','192','.10',lambda t:1+14/t)
 tails()
def tails():
 # qr(t)*e^{t/8} decreases for t>=191; freeze the factor at each onset-1.
 # L^j times the underlying pointwise loss decreases after these onsets.
 def scaled_loss(start,j):
  l=I(start);y=l-1
  return l**j*qr(y)*(l/y+2*U(l)+qr(y))
 assert exp(I('36.72')).below(115*10**14)
 assert scaled_loss(192,6).below(co[6])
 assert all(c>0 for c in co[4:17])
 base=300
 neg=sum((F(-co[k],base**(k-16)) for k in range(17,35) if co[k]<0),F(0))
 assert neg<F(co[16],2)
 # All the exact profiles through order 15; use the next coefficient for slack.
 for k,start in enumerate([223,256,290,325,360,396,431,467,503,547],6):
  assert scaled_loss(start,k+1).below(F(co[k+1],2) if k==15 else co[k+1]),(k,start)
 # Earlier profiles before the first exact order-six onset.
 for start,k,j,c in [(194,6,7,40),(201,6,8,F(975,10)),(220,6,7,143)]:
  rhs=(co[k]-c)*start**(j-k)+sum(co[i]*start**(j-i) for i in range(k+1,j+1))
  assert scaled_loss(start,j).below(rhs),(start,j)
 # retain half of order 16 minus a fixed quarter from coefficient and error:
 assert scaled_loss(570,16).below(F(co[16],4))
 print('Ramanujan exact higher-order and analytic tail checks: OK',flush=True)
def count(n):
 r=isqrt(n)
 v=[n//i for i in range(1,r+1)]+list(range(n//r-1,0,-1));s={i:i-1 for i in v}
 for q in range(2,r+1):
  if s[q]==s[q-1]:continue
  z=s[q-1];q2=q*q
  for i in v:
   if i<q2:break
   s[i]-=s[i//q]-z
 return s[n]
def endpoint():
 A0=38358837682;e=exp(1)
 assert ((A0+I(0,1))/e-14111427770).above(0)
 assert ((A0+I(0,1))/e-14111427770).below(1)
 m=count(A0);n=count(14111427770)
 assert (m,n)==(1644673232,632207037)
 for d,b in [('0.21792',-1),('0.21794',1)]:
  x=A0+I(d);v=e*x*n/ln(x)-m*m
  assert v.above(0) if b==1 else v.below(0)
 print('Ramanujan exact last real crossing bracket:',A0,m,n,'+.21792..+.21794')
if __name__=='__main__':
 import sys
 if 'endpoint' in sys.argv:endpoint()
 elif 'tails' in sys.argv:tails()
 else:ranu()
