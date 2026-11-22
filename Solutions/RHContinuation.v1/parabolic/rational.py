"""Directed dyadic rational arithmetic; all acceptance checks survive Python optimization.
Adapted from the frozen NL bounds.py, replacing assertions with explicit errors.
"""
from fractions import Fraction as F
from pathlib import Path
import math
SCALE=2**256
def need(ok,msg):
    if not ok:raise ValueError(msg)
class I:
    def __init__(self,l,h=None):
        l=F(l);h=l if h is None else F(h);need(l<=h,'ordered interval')
        self.l=F((l*SCALE).__floor__(),SCALE);self.h=F((h*SCALE).__ceil__(),SCALE)
    def __add__(self,r):
        r=cast(r);return I(self.l+r.l,self.h+r.h)
    __radd__=__add__
    def __neg__(self):return I(-self.h,-self.l)
    def __sub__(self,r):return self+-cast(r)
    def __rsub__(self,r):return cast(r)+-self
    def __mul__(self,r):
        r=cast(r);a=[u*v for u in(self.l,self.h)for v in(r.l,r.h)];return I(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,r):
        r=cast(r);need(r.l*r.h>0,'denominator excludes zero');return self*I(1/r.h,1/r.l)
    def __rtruediv__(self,r):return cast(r)/self
    def __pow__(self,n):
        need(type(n)is int,'integer power')
        if n<0:return(1/self)**(-n)
        if n==0:return I(1)
        if n%2:return self*self**(n-1)
        u=self**(n//2);return u*u
    def lt(self,r):return self.h<cast(r).l
    def gt(self,r):return self.l>cast(r).h
    def row(self):return {'lower':str(self.l),'upper':str(self.h),'upper_ceiling_1e9':str(F((self.h*10**9).__ceil__(),10**9))}
def cast(r):return r if isinstance(r,I)else I(r)
def exp_pt(t,N=58):
    if t<0:return 1/exp_pt(-t,N)
    k=0
    while t>1:t/=2;k+=1
    q=I(t);term=s=I(1)
    for j in range(1,N+1):term=term*q/j;s+=term
    rem=(term*q/(N+1))/(1-F(1,N+2));v=I(s.l,(s+rem).h)
    for _ in range(k):v=v*v
    return v
def exp(t):
    t=cast(t);return I(exp_pt(t.l).l,exp_pt(t.h).h)
def log_unit(x,N=58):
    need(1<=x<=2,'log reduced argument');u=(I(x)-1)/(I(x)+1);u2=u*u;un=u;v=I(0)
    for k in range(N):v+=un/(2*k+1);un*=u2
    rem=un/((2*N+1)*(1-u2));return I((2*v).l,(2*(v+rem)).h)
LOG2=log_unit(F(2))
def log_pt(x):
    need(x>0,'positive log argument')
    if x<1:return-log_pt(1/x)
    b=x.numerator.bit_length()-x.denominator.bit_length();b-=x<2**b
    return b*LOG2+log_unit(x/F(2)**b)
def log(x):
    x=cast(x);return I(log_pt(x.l).l,log_pt(x.h).h)
def atan_inverse(q,n=45):
    x=F(1,q);s=sum((-1)**k*x**(2*k+1)/(2*k+1)for k in range(n));t=s+(-1)**n*x**(2*n+1)/(2*n+1);return I(min(s,t),max(s,t))
PI=16*atan_inverse(5)-4*atan_inverse(239)
def trig(t,N=20):
    t=F(t);need(0<t<=F(1,100),'Taylor argument');d=t*t;co=F(1);si=t;tc=F(1);ts=t
    for j in range(1,N):tc*=-d/((2*j-1)*(2*j));ts*=-d/((2*j)*(2*j+1));co+=tc;si+=ts
    c2=co-tc*d/((2*N-1)*(2*N));s2=si-ts*d/((2*N)*(2*N+1));return I(min(si,s2),max(si,s2)),I(min(co,c2),max(co,c2))
