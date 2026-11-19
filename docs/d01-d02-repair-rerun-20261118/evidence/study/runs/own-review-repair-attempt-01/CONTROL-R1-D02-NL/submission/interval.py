"""Exact fixed-point intervals. All endpoint operations outward rounded."""
from fractions import Fraction
from functools import lru_cache
S=10**125
def ceil(a,b): return -((-a)//b)
class I:
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.a,self.b=a,b;return
  if isinstance(a,I):self.a,self.b=a.a,a.b;return
  f,g=Fraction(a),Fraction(a if b is None else b)
  self.a=f.numerator*S//f.denominator;self.b=ceil(g.numerator*S,g.denominator)
 def __add__(self,x):
  x=I(x);return I(self.a+x.a,self.b+x.b,True)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a,True)
 def __sub__(self,x):return self+-I(x)
 def __rsub__(self,x):return I(x)+-self
 def __mul__(self,x):
  x=I(x);z=[a*b for a in (self.a,self.b) for b in (x.a,x.b)]
  return I(min(z)//S,ceil(max(z),S),True)
 __rmul__=__mul__
 def __truediv__(self,x):
  x=I(x);assert x.a*x.b>0
  return self*I(S*S//x.b,ceil(S*S,x.a),True)
 def __rtruediv__(self,x):return I(x)/self
 def __pow__(self,n):
  if n<0:return 1/(self**(-n))
  y=I(1);z=self
  while n:
   if n%2:y=y*z
   n//=2
   if n:z=z*z
  return y
 def lo(self):return I(self.a,self.a,True)
 def hi(self):return I(self.b,self.b,True)
 def yes(self):return self.a>0
 def __repr__(self):return repr((self.a/S,self.b/S))
def mn(a,b):
 a,b=I(a),I(b);return I(min(a.a,b.a),min(a.b,b.b),True)
def mx(a,b):
 a,b=I(a),I(b);return I(max(a.a,b.a),max(a.b,b.b),True)
@lru_cache(maxsize=120000)
def ex(q):
 q=Fraction(q)
 if q<0:return 1/ex(-q)
 if q>1:
  n=q.numerator//q.denominator
  return ex(1)**n*ex(q-n)
 x=I(q);term=I(1);y=term
 for j in range(1,65):term=term*x/j;y+=term
 y=I(y.a,(y+term/32).b,True)  # omitted sum < last term / 64
 return y
def exp(x):
 x=I(x);return I(ex(Fraction(x.a,S)).a,ex(Fraction(x.b,S)).b,True)
def log_unit(q,n=150):
 z=I((q-1)/(q+1));w=z*z;v=z;y=v
 for j in range(1,n):v*=w;y+=v/(2*j+1)
 return I((2*y).a,(2*y+3*v*w).b,True)
LOG2=log_unit(Fraction(2))
@lru_cache(maxsize=1000)
def ln(q):
 q=Fraction(q);assert q>0
 if q<1:return -ln(1/q)
 n=q.numerator.bit_length()-q.denominator.bit_length()
 if q<2**n:n-=1
 return n*LOG2+log_unit(q/(2**n))
