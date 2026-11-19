"""Exact sieve; directed interval certification of local Dusart crossings."""
from intervals import I,F,log,exp,_log1,L2,B
from math import isqrt, factorial
N=8000000
tab=[_log1(I(F(256+j,256))) for j in range(256)]
def lf0(n):
    k=n.bit_length()-B.bit_length()
    y=F(n,B)*F(2)**-k
    j=int((y-1)*256)
    w=I(y/F(256+j,256))
    z=(w-1)/(w+1);zz=z*z;a=t=z
    for r in range(1,7):
        t=t*zz;a+=t/(2*r+1)
    return k*L2+tab[j]+2*a+I(0,F(4,513**15))
def lf(x):
    x=I(x)
    u=lf0(x.l)
    return I(u.l,lf0(x.h).h if x.h!=x.l else u.h,True)
def primes(N):
    a=bytearray(b"\1")*(N+1);a[:2]=b"\0\0"
    for p in range(2,isqrt(N)+1):
        if a[p]:a[p*p:N+1:p]=b"\0"*((N-p*p)//p+1)
    return [p for p in range(2,N+1) if a[p]]
def hpart(p):
    if p<1000: return -lf(1-F(1,p))-F(1,p)
    h=sum(F(1,j*p**j) for j in (2,3,4))
    return I(h,h+F(2,5*p**5))
def main():
    g=100000
    gamma=sum(I(F(1,k)) for k in range(1,g+1))-log(g)-F(1,2*g)+I(0,F(1,6*g**3)+F(1,12*g**2))
    ll=log(N);eps=F(1,5)/ll**2
    z=sum((-1)**j*factorial(j)/ll**j for j in range(8))/(2*N*ll)
    rr=factorial(8)/(2*N*ll**9)
    es=3*eps/(2*N*ll)
    hs=z+I(-F(es.h,B),F((es+rr+3/(N*N*ll)).h,B))
    ew=3*eps/N
    ws=I(F(1,N))-I(0,F(ew.h,B))+I(0,F((ew+F(6,N*N)).h,B))
    s=q=w=M=K=I(0)
    prev={}
    ends=[912559,2278379]
    plist=primes(N)
    assert [p for p in plist if 912559<=p<=912560]==[912559]
    assert [p for p in plist if 2278379<=p<=2278383]==[2278379]
    for p in plist:
        l=lf(p);h=hpart(p)
        s+=F(1,p);w+=l/p;q+=F(1,p)+h;M+=h;K+=l/(p*(p-1))
        if p in ends:prev[p]=(s,w,q)
    M=gamma-M-hs;K=gamma+K+ws
    print('constants',gamma.pt(),M.pt(),K.pt())
    def test(t,j):
        l=log(t);s,w,q=prev[ends[0] if j==1 else ends[1]]
        if j==0:return (s-M-log(l))*l**3
        if j==1:return (w+K-l)*l**2
        d=q-gamma-log(l)
        return (exp(d)-1 if j==2 else 1-exp(-d))*l**3
    for j,(k,eta) in enumerate([(2278379,F('.2')),(912559,F('.3')),(2278379,F('.2')),(2278379,F('.2'))]):
        end=912560 if j==1 else 2278383 if j==0 else 2278382
        print(j,'at p,join',test(k,j).pt(),test(end,j).pt())
        l=log(end)
        if j==0:err=prev[k][0]-M-log(l)
        elif j==1:err=prev[k][1]+K-l
        else:err=prev[k][2]-gamma-log(l)
        assert I(0).lt(err) and err.lt(F(1,100))
        assert I(eta).lt(test(k,j)) and test(end,j).lt(eta)
        assert I(10).lt(log(k)) and test(k,j).lt(1)
        lo=hi=None
        for i in range((end-k)*1000+1):
            x=k+F(i,1000)
            u=test(x,j)
            if I(eta).lt(u):lo=x
            if u.lt(eta):hi=x;break
        assert (lo,hi)==tuple(map(F,[('2278382.112','2278382.114'),('912559.997','912559.998'),('2278381.711','2278381.712'),('2278381.575','2278381.576')][j]))
        print('crossing bracket',j,str(lo),str(hi),float(lo),float(hi))
if __name__=='__main__':main()
