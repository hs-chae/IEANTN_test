"""Certified fixed-point intervals, integer arithmetic only (Python 3.10)."""
from fractions import Fraction as F
from math import factorial
B=1<<192
def ceil(n,d): return -((-n)//d)
class I:
    __slots__=('l','h')
    def __init__(self,l=0,h=None,raw=False):
        if raw: self.l,self.h=l,h; return
        if isinstance(l,I):
            self.l,self.h=l.l,l.h; return
        a,b=F(l),F(l if h is None else h)
        self.l=a.numerator*B//a.denominator
        self.h=ceil(b.numerator*B,b.denominator)
    def __add__(a,b):
        b=I(b);return I(a.l+b.l,a.h+b.h,True)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l,True)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);p=[a.l*b.l,a.l*b.h,a.h*b.l,a.h*b.h]
        return I(min(p)//B,ceil(max(p),B),True)
    __rmul__=__mul__
    def inv(a):
        assert not a.l<=0<=a.h
        return I(B*B//a.h,ceil(B*B,a.l),True)
    def __truediv__(a,b):return a*I(b).inv()
    def __rtruediv__(a,b):return I(b)*a.inv()
    def __pow__(a,k):
        if k<0:return a.inv()**-k
        t=I(1)
        while k:
            if k&1:t=t*a
            k>>=1
            if k:a=a*a
        return t
    def lt(a,b):return a.h<I(b).l
    def pt(a):return a.l/B,a.h/B
def _exp(n):
    # for negative inputs use a reciprocal only up to a range giving
    # representable relative precision; tiny values can be bounded by an ulp.
    if n<-140*B:return I(0,1,True) # exp(-140)<2^-192 since e^.7>2
    if n<0:return _exp(-n).inv()
    s=0
    while n>B//2:
        s+=1
        # do not round in reduction
        if n<=B*(1<<s)//2:break
    y=I(F(n,B<<s))
    t=v=I(1)
    for j in range(1,48):
        t=t*y/j;v=v+t
    v+=I(0,F(2,2**48*factorial(48)))
    for j in range(s):v=v*v
    return v
def exp(a):
    a=I(a)
    return I(_exp(a.l).l,_exp(a.h).h,True)
def _log1(y):
    # 1<=y<=2. atanh series, z< 1/3 except for y=2 (allowed).
    z=(y-1)/(y+1);w=z*z;s=t=z
    for j in range(1,65):
        t=t*w;s+=t/(2*j+1)
    return 2*s+I(0,F(4,3**131))
L2=_log1(I(2))
def _log(n):
    assert n>0
    k=n.bit_length()-B.bit_length()
    v=F(n,B)*(F(2)**-k)
    assert 1<=v<2
    return _log1(I(v))+k*L2
def log(a):
    a=I(a)
    return I(_log(a.l).l,_log(a.h).h,True)
def atan(z):
    z=F(z);s=sum((-1)**j*z**(2*j+1)/(2*j+1) for j in range(32))
    return I(s,s+z**65/65)
PI=16*atan(F(1,5))-4*atan(F(1,239))
