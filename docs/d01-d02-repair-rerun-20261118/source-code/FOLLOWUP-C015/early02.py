"""Input-independent use of a stronger reported finite pi bound and local sieve."""
from applications02 import *
from mertens import sieve
from math import isqrt
N=18
U=[fac(j) for j in range(N)]+[5*fac(N)]
CO=[sum(fac(k)*comb(j,k) for k in range(min(j,N-1)+1))-
    sum(U[k]*U[j-k] for k in range(N+1) if 0<=j-k<=N) for j in range(2*N+1)]
assert CO[:4]==[0]*4
def early_boot():
    A=I(26)
    lowp=r.barrier(A,N)
    true=r.ei(A)*ex(-A)
    assert low(true,lowp) and low(lowp+5*fac(N)/A**(N+1),true)
    assert 5*(1-F(N+1,26))>1
    a=I(2).log()
    assert low(2,r.ei(a))
    assert low(r.ei(a),0)
    assert low(19*I(10).log(),'43.74')
def reported_pi(L):
    return (I('1.95')+I('3.9')/L+I('19.5')/L**2)*ex(-L/2)+2*L*ex(-L)

def pii(L,reported=True):
    assert 26*S<=L.lo<=L.hi and 100*L.hi<=4374*S
    vals=[]
    if reported:vals.append(reported_pi(L))
    # Need only the LOWER pi boundary in this part of the application.
    if 10*L.hi<=299*S:
        c=I('1.751000147')*ex(-L/2)+I('1.78')*ex(-2*L/3)
        vals.append(c+integ_split(L,1))
    if L.lo>=33*S:vals.append(pi_bound(L,1))
    assert vals
    return m.mn(*vals)
def pi_book(L):
    e=pi_bound(L,1)
    return m.mn(e,reported_pi(L)) if 26*S<=L.lo and 100*L.hi<=4374*S else e

def ec(a,b,c,reported=True):
    a,b=F(a),F(b)
    assert 27<=a<b<=F('43.74')
    co=CO[4:].copy()
    for j,v in enumerate(c):co[j]-=F(v)
    def test(a,b):
        L=bracket(a,b)
        M=sum(v/L**i for i,v in enumerate(co) if v)-L**4*(L/(L-1))*pii(L-1,reported)
        if low(M,0):return
        if b-a<F(1,65536):raise ValueError((a,b,M))
        c=(a+b)/2
        test(a,c);test(c,b)
    grid=sorted({a,b,*[F(j) for j in range(int(a)+1,int(b)+1) if a<j<b],*[j for j in [F('30.9'),F(34)] if a<j<b]})
    for x,y in zip(grid,grid[1:]):test(x,y)
    print('early R',a,b,c,reported,flush=True)
def seg(a,b,pr):
    s=bytearray(b-a+1)
    for p in pr:
        if p*p>b:break
        k=max(p*p,-(-a//p)*p)
        if k<=b:s[k-a::p]=b'\1'*((b-k)//p+1)
    return s
def local():
    n=38358837682;m0=14111427770;b=632207037;c=1644673232
    H=100000
    pn=sieve(isqrt(n+H))
    a=seg(n+1,n+H,pn)
    v=seg(m0+1,m0+H,pn)
    m=m0
    for x in range(n+1,n+H+1):
        if not a[x-n-1]:c+=1
        u=I(x)/E; k=u.lo//S
        assert k==u.hi//S and m<=k<=m0+H
        while m<k:
            m+=1
            if not v[m-m0-1]:b+=1
        L=I(x).log()
        R=E*x/L*b-c*c
        assert low(R*L**6/(x+1)**2,I('0.00000752'))
    print('local R [n+1,n+100001): margin .00000752',flush=True)

