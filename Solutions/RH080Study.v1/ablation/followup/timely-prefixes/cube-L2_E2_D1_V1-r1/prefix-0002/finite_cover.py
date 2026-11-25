"""Exact all-real finite certificate. Not a source-first verification."""
from bisect import bisect_right
from math import isqrt
from fractions import Fraction as Q

M=4096
PRIMES=[p for p in range(2,13**3) if all(p%d for d in range(2,isqrt(p)+1))]
S=10**10

def log_lower(j):
    # log(j/M)=v*log 2 + log r, 1 <= r < 2.
    d=M
    v=0
    while j>=2*d:
        v+=1
        d*=2
    def part(a,b):
        z=Q(a-b,a+b)
        return 2*sum(z**(2*i+1)/(2*i+1) for i in range(9))
    l=part(j,d)+v*L2
    return l.numerator*S//l.denominator

L2=2*sum(Q(1,3)**(2*i+1)/(2*i+1) for i in range(9))
RUN=[(3*M//2,2*M,Q(".70")),(2*M,3*M,Q(".84")),(3*M,12*M,Q(".94"))]
for a,b,c in RUN:
    for j in range(a,b):
        lm=(j+1)**3//M**3
        rm=((j+M)**3-1)//M**3
        k=bisect_right(PRIMES,rm)-bisect_right(PRIMES,lm)
        assert k*log_lower(j)*M*M*c.denominator > c.numerator*(j+1)**2*S
    print(Q(a,M),Q(b,M),c, "certified")
