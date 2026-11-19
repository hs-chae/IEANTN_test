# Exact pi(n) by counting integers free of primes <= floor(n**(1/4)).
from functools import lru_cache
from bisect import bisect_right
from math import isqrt
from decimal import Decimal, localcontext
from fractions import Fraction as F

N=38358837682
S=isqrt(N+1)+1
sieve=bytearray([1])*(S+1)
sieve[:2]=b'\0\0'
for j in range(2,isqrt(S)+1):
    if sieve[j]:
        sieve[j*j::j]=b'\0'*((S-j*j)//j+1)
pr=[j for j in range(S+1) if sieve[j]]
@lru_cache(None)
def phi(n,a):
    if a==0:return n
    if n<pr[a-1]:return 1
    if n<=S and pr[a-1]**2>n:return max(1,bisect_right(pr,n)-a+1)
    return phi(n,a-1)-phi(n//pr[a-1],a-1)

@lru_cache(None)
def pi(n):
    if n<=S:return bisect_right(pr,n)
    a=pi(isqrt(isqrt(n)))
    b=pi(isqrt(n))
    ans=phi(n,a)+a-1
    for i in range(a,b):
        y=n//pr[i]
        ans-=pi(y)-i
        for j in range(i,pi(isqrt(y))):
            ans-=pi(y//pr[j])-j
    return ans

if __name__=='__main__':
    den=sum((F(1,1)/__import__('math').factorial(k) for k in range(41)),F(0))
    hi=den+F(1,40*__import__('math').factorial(40))
    lo=den
    m=N//hi
    assert (N+1)//lo==m
    print(N,m,pi(N),pi(m),pi(N+1),flush=True)
    with localcontext() as c:
        c.prec=65
        e=Decimal(1).exp()
        for n in [N-1,N,N+1]:
            x=Decimal(n)
            print(n,e*x/x.ln()*pi(m)-pi(N)**2)
