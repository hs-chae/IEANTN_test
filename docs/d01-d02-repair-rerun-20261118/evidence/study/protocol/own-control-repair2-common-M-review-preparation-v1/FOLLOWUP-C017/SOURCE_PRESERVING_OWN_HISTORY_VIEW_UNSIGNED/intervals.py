"""Finite interval checks, Python 3.10, stdlib only.
Decimal basic operations use directed rounding. Decimal exp/ln are
specified correctly rounded to nearest; one neighbor each way encloses.
"""
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
LO=Context(prec=55,rounding=ROUND_FLOOR)
HI=Context(prec=55,rounding=ROUND_CEILING)
NE=Context(prec=55,rounding=ROUND_HALF_EVEN)
class I:
    __slots__=('l','r')
    def __init__(self,l=0,r=None):
        if isinstance(l,I):
            self.l,self.r=l.l,l.r
        else:
            self.l,self.r=D(l),D(l if r is None else r)
        assert self.l<=self.r
    def __repr__(self): return f'[{self.l}, {self.r}]'
    def __add__(x,y):
        y=I(y)
        return I(LO.add(x.l,y.l),HI.add(x.r,y.r))
    __radd__=__add__
    def __neg__(x): return I(x.r.copy_negate(),x.l.copy_negate())
    def __sub__(x,y): return x+-I(y)
    def __rsub__(x,y): return I(y)+-x
    def __mul__(x,y):
        y=I(y)
        if x.l>=0 and y.l>=0: return I(LO.multiply(x.l,y.l),HI.multiply(x.r,y.r))
        if y.l>=0 and x.r<=0: return I(LO.multiply(x.l,y.r),HI.multiply(x.r,y.l))
        if x.l>=0 and y.r<=0: return y*x
        if x.r<=0 and y.r<=0: return (-x)*(-y)
        v=[(a,b) for a in (x.l,x.r) for b in (y.l,y.r)]
        return I(min(LO.multiply(a,b) for a,b in v),max(HI.multiply(a,b) for a,b in v))
    __rmul__=__mul__
    def __truediv__(x,y):
        y=I(y)
        assert y.l>0 or y.r<0
        return x*I(LO.divide(D(1),y.r),HI.divide(D(1),y.l))
    def __rtruediv__(x,y): return I(y)/x
    def __pow__(x,n):
        assert isinstance(n,int)
        if n<0:return 1/(x**(-n))
        out=I(1)
        while n:
            if n%2: out=out*x
            n//=2
            if n: x=x*x
        return out
    def exp(x):
        return I(NE.next_minus(NE.exp(x.l)),NE.next_plus(NE.exp(x.r)))
    def ln(x):
        assert x.l>0
        return I(NE.next_minus(NE.ln(x.l)),NE.next_plus(NE.ln(x.r)))
    def power(x,y): return (x.ln()*y).exp()
def mini(*v):
    v=[I(x) for x in v]
    return I(min(x.l for x in v),min(x.r for x in v))
def maxi(*v):
    v=[I(x) for x in v]
    return I(max(x.l for x in v),max(x.r for x in v))
def pi_interval():
    # Machin identity via tangent addition, alternating arctangent series.
    def at(q):
        v=sum((I((-1)**j)/((2*j+1)*q**(2*j+1)) for j in range(45)),I())
        b=I(1)/(91*q**91)
        return v-I(0,b.r)
    return 16*at(5)-4*at(239)
PI=pi_interval()
E=I(1).exp()
LN2=I(2).ln()

def expm1(x):
    x=I(x)
    if max(x.r,x.l.copy_negate())<D('.01'):
        z=maxi(-x,x)
        return x+I(0,(I('.51')*z*z).r)
    return x.exp()-1
