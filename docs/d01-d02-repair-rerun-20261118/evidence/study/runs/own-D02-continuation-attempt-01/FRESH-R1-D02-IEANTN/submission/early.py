"""Certified small Mertens bridge: all real x in [2,2278383]."""
from verify import I,D
from math import isqrt
N=2278383
def primes(n):
    s=bytearray(b"\1")*(n+1)
    s[:2]=b"\0\0"
    for i in range(2,isqrt(n)+1):
        if s[i]:
            j=i*i
            s[j::i]=bytes((n-j)//i+1)
    return (i for i in range(2,n+1) if s[i])
def mag(t): return max(t.b,t.a.copy_negate())
def main():
    n=10000
    a=sum(I(1)/j for j in range(1,n+1))-I(n).log()-I(1)/(2*n)
    gamma=a+I(0,(I(1)/n**2).b)
    A=B=C=I(0)
    for p in primes(N):
        C+=-(1-I(1)/p).log()-I(1)/p
        B+=I(p).log()/(p*(p-1))
    MT=gamma-C-I(0,(I(1)/(2*N)).b)
    B3=gamma+B+I(0,((1+I(N).log())/(N-1)).b)
    # On each prime-free half-open interval normalize by its right endpoint.
    A=B=Q=I(0)
    result={s:[D(0)]*4 for s in [2,100,1000,10000,100000,500000,900000,1000000,2000000]}
    left=2
    tleft=I(left).log()
    def check(right,tright):
        cache={}
        for s,m in result.items():
            if right<s:continue
            key=max(left,s)
            if key not in cache:
                l=tleft if left>=s else I(s).log()
                u=tright
                q=I(l.a,u.b)
                d=Q-gamma-q.log()
                pa=max((I(d.a.copy_negate()).exp()-1).b,(1-I(d.b.copy_negate()).exp()).b)
                pb=max((I(d.b).exp()-1).b,(1-I(d.a).exp()).b)
                sb=I(mag(A-MT-q.log()))*u**3
                sl=I(mag(B+B3-q))*u**2
                cache[key]=((I(pa)*u**3).b,(I(pb)*u**3).b,sb.b,sl.b)
            for i,v in enumerate(cache[key]):m[i]=max(m[i],v)
    for p in primes(N):
        t=I(p).log()
        if p>2: check(p,t)
        r=I(1)/p
        A+=r; B+=t/p; Q-=(1-r).log()
        left=p;tleft=t
    check(N,I(N).log())
    print('gamma, M, B3',gamma,MT,B3)
    for s,m in result.items(): print('early scaled maxima upper',s,*m)
    return result
if __name__=='__main__':
    main()
