#!/usr/bin/python3.10
"""Exact, terminating all-order onset construction; see orders.md."""
from fractions import Fraction as F
from math import factorial as fac, comb
import sys

def twonegn(n):
    assert n>=0
    return F(1,1<<n)
def coeff(j):
    n=j+4
    return sum((fac(r)*comb(n,r)-fac(r)*fac(n-r) for r in range(n+1)))
def onset(j):
    assert j>=0
    n=j+6
    a=max(302,8*(j+6)+2,4*(n+2)+1)
    P={}
    lc={i:fac(i-1) for i in range(1,n+2)}
    up=lc|{n+2:4*fac(n+1)}
    for k in range(2,2*(n+2)+1):
        P[k-6]=sum(v*comb(k-2,i-1) for i,v in lc.items() if i<k)-sum(v*up.get(k-i,0) for i,v in up.items())
    for k in range(j+1):
        assert P[k]==coeff(k)
        P[k]=0
    assert P[j+1]==coeff(j+1)>0
    # Rational, terminating search. V bounds the two pi errors evaluated at t=a or a-1.
    def V(t):
        return F("0.0161")*(1+F("1.16")/t)*twonegn(t//8)+F("2e-18")*F(t,300)*twonegn(t-300)
    while True:
        b=a-1
        unit=F(fac(n+1),b**(n+2))
        anchor=(3+sum(lc.values()))*twonegn(b-1)
        if anchor >= unit/4 or twonegn(b//2)>=F(1,b**(n+2)):
            a*=2
            continue
        if sum(F(v,a**(i-1)) for i,v in up.items())>=2:
            a*=2
            continue
        low=P[j+1]+sum(F(v,a**(k-j-1)) for k,v in P.items() if k>j+1 and v<0)
        E=a**(j+5)*(F(a,a-1)*V(a-1)+V(a)*(4+V(a)))
        if low>E:
            return a
        a*=2

if __name__=='__main__':
    for arg in sys.argv[1:]:
        j=int(arg)
        print(j,onset(j))
