"""Exact integer/rational audit for the last real Ramanujan crossing."""
from fractions import Fraction as F
from math import isqrt, factorial

def prime_count(n):
    if n < 2:
        return 0
    r = isqrt(n)
    vs = [n//i for i in range(1,r+1)]
    vs += list(range(vs[-1]-1,0,-1))
    s = {v:v-1 for v in vs}
    for p in range(2,r+1):
        j = s[p-1]
        if s[p] > j:
            for v in vs:
                if v < p*p:
                    break
                s[v] -= s[v//p] - j
    return s[n]

def log_unit(x, n=55):
    assert 1 <= x <= 2
    a=(x-1)/(x+1)
    partial=2*sum(a**(2*k+1)/ (2*k+1) for k in range(n))
    return partial,partial+2*a**(2*n+1)/((2*n+1)*(1-a*a))

def log(x):
    x=F(x)
    assert x>=1
    b=x.numerator.bit_length()-x.denominator.bit_length()
    b-= x < 2**b
    lo,hi=log_unit(x/2**b)
    l2,h2=log_unit(F(2))
    return lo+b*l2,hi+b*h2

def efun(n=50):
    lo=sum(F(1,factorial(k)) for k in range(n+1))
    return lo,lo+F(n+2,(n+1)*factorial(n+1))

def run():
    k=38358837682
    e0,e1=efun()
    ql=k//e1
    qr=(k+1)//e0
    print('floor(x/e) enclosure:',ql,qr,flush=True)
    pk=prime_count(k)
    pa=prime_count(ql)
    pb=prime_count(qr) if qr!=ql else pa
    print('pi counts:',pk,pa,pb,flush=True)
    assert pa == pb
    def cmp(x):
        l0,l1=log(x)
        if e1*x*pb < l0*pk*pk: return -1
        if e0*x*pa > l1*pk*pk: return 1
        raise ArithmeticError('insufficient precision')
    print('endpoint signs:',cmp(k),cmp(k+1),flush=True)
    assert cmp(k)==-1 and cmp(k+1)==1
    den=10**14
    lo,hi=0,den
    while hi-lo > 1:
        mid=(lo+hi)//2
        if cmp(k+F(mid,den))<0: lo=mid
        else: hi=mid
    assert 0<lo<hi<den
    print(f'root in ({k}.{lo:014d}, {k}.{hi:014d})')

if __name__=='__main__':run()
