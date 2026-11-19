"""Extended finite Mertens product and reciprocal sum profiles (integer intervals)."""
from verify import I,fac
from early import primes,N
from weighted import S,N1,scale,ceildiv
from decimal import Decimal as D

def logpair(args):
    n=stop=0
    for p in args:
        if p>=stop:
            n=p;stop=n+max(1,n//2048)
            z=I(n).log()
            a,b=scale(z)
            c,d=scale(z.log())
            n2=n*n;n3=n2*n
        h=p-n;h2=h*h
        l=a+S*(2*n*h-h2)//(2*n2)
        u=b+ceildiv(S*(6*n2*h-3*n*h2+2*h*h2),6*n3)
        # Ratio of the increment of log p to log n lies in [v/S,w/S].
        v=S*max(0,l-b)//b
        w=ceildiv(S*(u-a),a)
        yield p,l,u,c+v-ceildiv(v*v,2*S),d+w

def series(p):
    if p<1000:
        return scale(-(1-I(1)/p).log()-I(1)/p)
    p2=p*p; p3=p2*p; p4=p3*p
    a=2*p2;b=3*p3;c=4*p4
    return S//a+S//b+S//c,ceildiv(S,a)+ceildiv(S,b)+ceildiv(S,c)+ceildiv(S,5*p4*(p-1))

def main():
    n=100000
    g=sum(I(1)/i for i in range(1,n+1))-I(n).log()-I(1)/(2*n)
    ga,gb=scale(g+I(0,(I(1)/n**2).b))
    ma,mb=ga,gb
    for p in primes(N):
        u,v=series(p)
        ma-=v;mb-=u
    z=I(N).log()
    # Main integral from d theta -> dt; alternating expansion of
    # 1/(1+w/z), integrated against e^{-w}. Extra log powers geometric.
    J0=sum((-1)**j*fac(j)/z**j for j in range(9))
    J1=J0-fac(9)/z**9
    low,high=J1/(2*N*z),J0/(2*N*z)
    eps=10/z**3*(1/(N*z)+high)
    ma-=scale(high+eps+I(1)/(6*N*(N-1)))[1]
    mb-=scale(low-eps)[0]
    A=B=Q=R=0
    ll=last_u=0
    # (log P positive error, log Q positive error, signed reciprocal-sum magnitude)
    thresholds={x:[0,0,0] for x in
        [2000000,2278000,2278300,2278380,D('2278381.5'),D('2278381.8'),D('2278381.9'),2278382,D('2278382.2'),2278383,3000000,5000000,10000000]}
    cl={s:scale(I(s).log().log())[0] for s in thresholds}
    cu={s:scale(I(s).log())[1] for s in thresholds}
    def check(p,l,u,v,w):
        if p<2000000:return
        nd=max(0,gb+w-Q)
        assert nd<S//10
        neg_exp=ceildiv(S*nd,S-nd)*u**3
        neg_rec=max(0,w+mb-A)*u**3
        for s,old in thresholds.items():
            if p<=s:continue
            lu=max(last_u,cu[s])
            d=max(0,R-ga-max(ll,cl[s]))
            assert d<S//10
            res=[max(d*lu**3,neg_exp),max(nd*u**3,ceildiv(S*d,S-d)*lu**3),
                 max(neg_rec,max(0,B-ma-max(ll,cl[s]))*lu**3)]
            for i,r in enumerate(res):old[i]=max(r,old[i])
    for p,l,u,v,w in logpair(primes(N1)):
        check(p,l,u,v,w)
        a,b=S//p,ceildiv(S,p)
        c,d=series(p)
        A+=a;B+=b;Q+=a+c;R+=b+d
        ll=v;last_u=u
    for p,l,u,v,w in logpair([N1]):
        check(p,l,u,v,w)
    assert (I(18).exp()).b<N1 and N1%2==0
    for x,m in thresholds.items():
        print('extended scaled upper',x,*[(I(i)/S**4).b for i in m])

if __name__=='__main__':main()
