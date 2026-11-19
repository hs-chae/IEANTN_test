"""Directed fixed-point intervals, integer arithmetic only (512 fraction bits)."""
from fractions import Fraction as F
S=1<<512
def ceildiv(n,d): return -((-n)//d)
class I:
    def __init__(self,x=0,hi=None):
        if hi is not None: self.lo,self.hi=x,hi;return
        if isinstance(x,I): self.lo,self.hi=x.lo,x.hi;return
        a=F(x)*S
        self.lo,self.hi=a.numerator//a.denominator,ceildiv(a.numerator,a.denominator)
    def __add__(a,b):
        b=I(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a): return I(-a.hi,-a.lo)
    def __sub__(a,b): return a+-I(b)
    def __rsub__(a,b): return I(b)+-a
    def __mul__(a,b):
        b=I(b);t=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(t)//S,ceildiv(max(t),S))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b)
        if b.hi<0:return (-a)/(-b)
        assert b.lo>0
        return I(min(a.lo*S//v for v in (b.lo,b.hi)),max(ceildiv(a.hi*S,v) for v in (b.lo,b.hi)))
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,n):
        assert isinstance(n,int)
        if n<0:return 1/(a**-n)
        y=I(1)
        while n:
            if n%2:y=y*a
            n//=2
            if n:a=a*a
        return y
    def L(a):return F(a.lo,S)
    def U(a):return F(a.hi,S)
    def __lt__(a,b):return a.hi<I(b).lo
    def __gt__(a,b):return a.lo>I(b).hi
    def __repr__(a):return f'[{float(a.L()):.14g},{float(a.U()):.14g}]'
def hull(l,u):return I(I(l).lo,I(u).hi)
def _log1(x):
    z=(x-1)/(x+1)
    w=z*z; term=z; y=I()
    for j in range(270):
        y+=term/(2*j+1);term*=w
    # |z| <= 1/2 suffices: 2* (1/2)^541/(1-(1/2)^2) < 2^-512
    assert z.L()>-F(1,2) and z.U()<F(1,2)
    return y*2+I(-1,1)
LN2=_log1(I(2))
def log(x):
    x=I(x)
    def one(t):
        assert t>0
        k=t.bit_length()-513
        z=I(F(t,S))
        if k>=0:z/=2**k
        else:z*=2**-k
        return _log1(z)+LN2*k
    return I(one(x.lo).lo,one(x.hi).hi)
def exp(x):
    x=I(x);k=0
    while max(abs(x.lo),abs(x.hi))>S:
        x=x/2;k+=1
    term=y=I(1)
    for j in range(1,100):
        term=term*x/j;y+=term
    # sum_(j>=100) |x|^j/j! <= (101/100)/100! < 2^-512
    y+=I(-1,1)
    for _ in range(k):y=y*y
    return y
PI=hull('3.141592653589793238462643383279502884','3.141592653589793238462643383279502885')
def pi_check():
    # Machin: 4 atan(1/5)-atan(1/239) = pi/4 by tangent addition and ranges.
    def atan(z):
        t=z; w=-z*z; s=I()
        for j in range(120):
            s += t/(2*j+1);t*=w
        return s+I(-1,1)  # 5^-241/241 < 2^-512
    # Use exact fractions here because accumulated fixed-point error need not
    # fit between consecutive decimal digits in the nominal PI enclosure.
    def atanq(z):
        t=sum((-1)**j*z**(2*j+1)/(2*j+1) for j in range(120))
        return t,t+z**241/241
    a,b=atanq(F(1,5));c,d=atanq(F(1,239))
    assert PI.L()<16*a-4*d and 16*b-4*c<PI.U()
