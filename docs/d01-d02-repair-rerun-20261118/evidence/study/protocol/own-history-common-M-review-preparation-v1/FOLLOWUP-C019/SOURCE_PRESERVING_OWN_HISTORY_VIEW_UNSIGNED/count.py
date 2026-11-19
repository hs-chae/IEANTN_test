"""Integer-only prime counting for the Ramanujan endpoint."""
from math import isqrt
def primepi(n):
    if n<2: return 0
    m=isqrt(n)
    # All distinct quotients floor(n/j), in decreasing order.
    v=[n//i for i in range(1,m+1) if n//i>m]+list(range(m,0,-1))
    D={x:x-1 for x in v}
    for p in range(2,m+1):
        if D[p]==D[p-1]: continue
        b=D[p-1]
        for x in v:
            if x<p*p:break
            D[x]-=D[x//p]-b
    return D[n]
def isprime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
if __name__=='__main__':
    from rigor import *
    x=38358837682
    e=exp(I(1)); n=14111427770
    assert I(x)/e>n and I(x+1)/e<n+1
    assert not isprime(x+1)
    a,b=primepi(x),primepi(n)
    assert (a,b)==(1644673232,632207037)
    def gap(v): return e*I(v)*b/log(v)-a*a
    left=F(x)+F(2179,10000); right=F(x)+F(218,1000)
    assert gap(left)<0 and gap(right)>0
    print('Endpoint counts:', a,b,'; rational root bracket offsets:',left-x,right-x)
