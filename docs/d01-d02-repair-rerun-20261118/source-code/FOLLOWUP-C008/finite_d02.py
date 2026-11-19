"""Input-independent finite normalizers and closed-cell product/sum join."""
from d02_cert import gamma,I,D,fac,E
from early import primes
from weighted import S,scale,ceildiv,logs
from smallprod import logpair,series
import sys

N=66000000
T=300000000 if "--extended" in sys.argv else N
ps=primes(N)
# Retain only an ordinary byte sieve in memory (do not store or emit a prime table).
ga,gb=scale(gamma())
ma,mb=ga,gb
ba,bb=ga,gb
for p,l,u in logs(ps):
    x,y=series(p); ma-=y;mb-=x
    d=p*(p-1); ba+=l//d;bb+=ceildiv(u,d)
z=I(N).log();eta=I(".2")/z**2
j=-(1-1/I(N)).log()
v=eta*(2/I(N-1)+j)
ba+=scale(j-v)[0];bb+=scale(j+v)[1]
j0=sum((-1)**i*fac(i)/z**i for i in range(9))/(2*N*z)
j1=j0-fac(9)/(2*N*z**10)
v=eta*(1/(N*z)+j0)
ma-=scale(j0+v+1/I(6*N*(N-1)))[1];mb-=scale(j1-v)[0]
print("normalizers outward fixed integers",ga,gb,ma,mb,ba,bb,flush=True)

prodpts=list(map(D,["2278381.72","2278381.73","2278381.74","2278381.75",
                    "2278381.8","2278382","2278382.1","2278382.12","2278382.15","2278383"]))
weightpts=list(map(D,["912559.996","912559.997","912559.9975","912559.998","912560"]))
shared=list(map(D,[10000000,12000000,15000000,18000000,20000000,25000000,30000000,40000000,50000000,60000000]))
if T>N:
    prodpts=[];weightpts=[]
    shared=list(map(D,[40000000,50000000,60000000,80000000,100000000,150000000,200000000]))
P=[(x,scale(I(x).log().log())[0],scale(I(x).log())[1],[0,0,0])
   for x in prodpts+shared]
W=[(x,*scale(I(x).log()),[0]) for x in weightpts+shared]
def exppos(v):
    assert 0<=v<S//10
    return v+ceildiv(v*v,2*(S-v))
lo=hi=Q=R=A=B=0
last_l=last_u=ll=0
def check(p,l,u,v,w):
    if p<W[0][0]:return
    posw=hi+bb; negw=u-lo-ba
    for x,a,d,Z in W:
        if p>x:
            h=max(0,posw-max(last_l,a))
            assert h<S
            Z[0]=max(Z[0], max(max(0,negw)*u*u,h*max(last_u,d)**2))
    if p<P[0][0]:return
    # Delta=log C_Q. Positive and negative signed extrema of scaled
    # log/sum errors occur at opposite endpoints.
    d=max(0,gb+w-Q)
    nd=exppos(d)*u**3
    nr=max(0,w+mb-A)*u**3
    for x,a,b,Z in P:
        if p>x:
            lu=max(last_u,b)
            h=max(0,R-ga-max(ll,a))
            Z[0]=max(Z[0], h*lu**3, nd)
            Z[1]=max(Z[1], exppos(h)*lu**3, d*u**3)
            r=max(0,B-ma-max(ll,a))
            assert r<S//3
            Z[2]=max(Z[2], r*lu**3,nr)
for p,l,u,v,w in logpair(primes(T)):
    check(p,l,u,v,w)
    lo+=l//p;hi+=ceildiv(u,p)
    a,b=S//p,ceildiv(S,p);c,d=series(p)
    A+=a;B+=b;Q+=a+c;R+=b+d
    last_l,last_u,ll=l,u,v
for p,l,u,v,w in logpair([T]):
    check(p,l,u,v,w)
assert T%2==0 and E(18).b<T
if T>N: assert E("19.5").b<T
for x,_,__,Z in P:print("prod",x,*[(I(zz)/S**4).b for zz in Z])
for x,_,__,Z in W:print("weighted",x,(I(Z[0])/S**3).b)
