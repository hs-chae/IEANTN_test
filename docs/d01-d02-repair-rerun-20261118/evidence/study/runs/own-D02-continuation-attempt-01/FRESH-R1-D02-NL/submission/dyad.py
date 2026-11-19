"""Exact integer directed interval arithmetic and certificates."""
from math import factorial as f, comb, isqrt
from fractions import Fraction as F
BITS=640
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
 n=max(1,(1024*t+S-1)//S);t=I(t,t,True)/n
 w=r=I(1)
 for j in range(1,49): w=w*t/j;r=r+w
 return (r+I(0,F(2,1024**49*f(49))))**n
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
