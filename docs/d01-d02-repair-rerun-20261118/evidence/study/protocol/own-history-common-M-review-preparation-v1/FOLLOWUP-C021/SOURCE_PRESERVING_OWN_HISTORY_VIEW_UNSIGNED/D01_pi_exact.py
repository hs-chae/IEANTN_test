
#!/usr/bin/python3.10
'''Prime count by floor-quotient sieve, with exact gap evaluation.'''
from math import isqrt
from check import I, exp, log, approx, lt, less, S
from fractions import Fraction as F

def pi(n):
    if n<2: return 0
    m=isqrt(n)
    small=[i-1 for i in range(m+1)]
    large=[0]+[n//j-1 for j in range(1,n//(m+1)+1)]
    nn=len(large)-1
    for p in range(2,m+1):
        if small[p]==small[p-1]: continue
        t=p*p; sp=small[p-1]
        for j in range(1,min(nn,n//t)+1):
            u=j*p
            large[j]-=(large[u] if u<=nn else small[n//u])-sp
        for j in range(m,t-1,-1):
            small[j]-=small[j//p]-sp
    return large[1] if nn else small[n]

def count_pair(x):
    from check import S
    y=I(x)/exp(I(1))
    assert y.a//S==y.b//S
    n=y.a//S
    return pi(x),pi(n),n

def check_gap(x,P,Q):
    return exp(I(1))*I(x)/log(I(x))*Q-P*P

if __name__=='__main__':
    seen=0
    for k in range(1,1001):
        if k>=2 and not any(k%d==0 for d in range(2,isqrt(k)+1)): seen+=1
        assert pi(k)==seen
    n=38358837682
    p,q,f=count_pair(n)
    assert (p,q,f)==(1644673232,632207037,14111427770)
    print(n,p,q,f,approx(check_gap(n,p,q)),flush=True)
    y=I(n+1)/exp(I(1))
    assert y.a//S==f==y.b//S
    assert (n+1)%2521==0
    less(-14736928,check_gap(n,p,q))
    less(check_gap(n,p,q),-14736927)
    less(52886500,check_gap(n+1,p,q))
    less(check_gap(n+1,p,q),52886501)
    l=log(n+1)
    less(67623427,exp(I(1))*q*(l-1)/l**2)
    a=F(n)+F(2179,10000); b=F(n)+F(2180,10000)
    less(check_gap(a,p,q),0)
    less(0,check_gap(b,p,q))
    print('last root n+.2179<r<n+.2180; exact floor and derivative tests passed')
