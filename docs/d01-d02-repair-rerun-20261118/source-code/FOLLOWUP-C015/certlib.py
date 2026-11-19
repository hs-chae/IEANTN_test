"""Integer fixed-point interval arithmetic, no external dependencies."""
from math import factorial
from functools import lru_cache

S = 10**36
def ceil(n,d):
    return -((-n)//d)

def _log1(a,b,n):  # input in [1,2], return a lower fixed point
    assert b <= a <= 2*b and b>0
    z = S*(a-b)//(a+b)
    z2 = z*z//S
    w=z; p=0
    for j in range(n):
        p+=w//(2*j+1)
        w=w*z2//S
    return 2*p

LOG2=_log1(2,1,42)
ANCHOR=[_log1(256+j,256,42) for j in range(256)]
ERR=512

def lnq(a,b):
    """Return enclosing integer endpoints of S log(a/b)."""
    assert a>0 and b>0
    e=a.bit_length()-b.bit_length()
    if e>=0: b <<= e
    else: a <<= -e
    if a<b:
        a <<= 1; e-=1
    assert b<=a<2*b
    j=(256*a)//b-256
    x=e*LOG2 + ANCHOR[j] + _log1(256*a,(256+j)*b,7)
    return x+min(e,0)*ERR, x+(max(e,0)+2)*ERR

class I:
    __slots__=('lo','hi')
    def __init__(self,x=0):
        if isinstance(x,I):
            self.lo,self.hi=x.lo,x.hi
        else:
            from fractions import Fraction
            q=Fraction(x)
            self.lo,self.hi=q.numerator*S//q.denominator,ceil(q.numerator*S,q.denominator)
    @staticmethod
    def raw(l,h):
        assert l<=h
        a=object.__new__(I);a.lo,a.hi=l,h
        return a
    def __add__(a,b):
        b = cv(b);return I.raw(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):
        return I.raw(-a.hi,-a.lo)
    def __sub__(a,b):
        return a+-cv(b)
    def __rsub__(a,b):
        return cv(b)+-a
    def __mul__(a,b):
        b=cv(b)
        if a.lo>=0 and b.lo>=0: return I.raw(a.lo*b.lo//S,ceil(a.hi*b.hi,S))
        t=[x*y for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
        return I.raw(min(t)//S,ceil(max(t),S))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=cv(b)
        if b.hi<0:return -a/-b
        assert b.lo>0
        if a.lo>=0:return I.raw(a.lo*S//b.hi,ceil(a.hi*S,b.lo))
        return I.raw(min(a.lo*S//y for y in (b.lo,b.hi)),max(ceil(a.hi*S,y) for y in (b.lo,b.hi)))
    def __rtruediv__(a,b):
        return cv(b)/a
    def __pow__(a,n):
        assert isinstance(n,int) and n>=0
        b=I(1)
        while n:
            if n&1:b*=a
            n//=2
            if n:a*=a
        return b
    def log(a):
        return I.raw(lnq(a.lo,S)[0],lnq(a.hi,S)[1])
    def exp(a):
        return I.raw(_exp(a.lo).lo,_exp(a.hi).hi)
    def __repr__(a):
        return str((a.lo/S,a.hi/S)) # diagnostics only

@lru_cache(None)
def _const(x):return I(x)
def cv(x):
    return x if isinstance(x,I) else _const(x)

@lru_cache(8192)
def _exp(v):
    if v<0: return 1/_exp(-v)
    y=I.raw(v,v); k=0
    while y.hi>S:
        y=y/2;k+=1
    t=s=I(1)
    for j in range(1,43):
        t=t*y/j
        s+=t
    s=I.raw(s.lo,s.hi+1)
    return s**(2**k)

def low(a,b):
    return cv(a).lo>cv(b).hi
def power(a,b):
    return (cv(a).log()*b).exp()
def bracket(a,b):
    return I.raw(cv(a).lo,cv(b).hi)

# Closed pi bounds via Machin's formula and alternating arctan.
def _atan(n):
    a=I(0)
    for i in range(31):
        a+=I((-1)**i)/((2*i+1)*n**(2*i+1))
    return I.raw(a.lo-1,a.hi+1)
PI=16*_atan(5)-4*_atan(239)
E=I(1).exp()
# gamma: corrected trapezoid approximants H_N-log N-1/(2N).
@lru_cache(None)
def gamma():
    N=100000
    h=sum(S//j for j in range(1,N+1))
    return I.raw(h,h+N)-I(N).log()-I(1)/(2*N)+bracket(0,I(1)/(12*(N-1)**2))

if __name__=='__main__':
    print('pi',PI,'e',E,'gamma',gamma())
