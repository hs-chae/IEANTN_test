"""Certified finite joins for the earlier uniform Mertens power profile."""
from d02_cert import I,D,gamma,fac
from weighted import S,scale,logs,ceildiv
from early import primes
from smallprod import logpair,series
from bisect import bisect_left

G=(50000,60000,70000,75000,78000,80000,90000,100000,104000,105000,106000,108000,110000,120000,140000,150000,180000,200000,250000,300000,400000,500000,700000,900000,1000000,1200000,1500000,2000000,2500000,3000000,4000000,5000000,6000000,8000000,10000000,12000000,15000000,20000000)
T=24154954                         # composite and > exp(17)
assert (I(17).exp()).b<T and T%2==0
n=100000
ga,gb=scale(gamma(n))
N=5000000
ma,mb=ga,gb
ba,bb=ga,gb
for p,l,u in logs(primes(N)):
    f,g=series(p)
    ma-=g; mb-=f
    ba+=l//(p*(p-1)); bb+=ceildiv(u,p*(p-1))
z=I(N).log()
j0=sum((-1)**i*fac(i)/z**i for i in range(9))/(2*N*z)
j1=j0-fac(9)/(2*N*z**10)
v=I(".2")/z**2*(1/(N*z)+j0)
ma-=scale(j0+v+1/I(6*N*(N-1)))[1];mb-=scale(j1-v)[0]
main=-(1-I(1)/N).log()
err=I('.2')/I(N).log()**2*(I(2)/(N-1)+main)
ba+=scale(main-err)[0]; bb+=scale(main+err)[1]
edges=[G[0]]
while edges[-1]<T:
    edges.append(min(T,edges[-1]+edges[-1]//200))
mult=[scale((I(t).log()/8).exp())[1] for t in edges]
clip={q:(scale(I(q).log())[0],scale(I(q).log().log())[0]) for q in G}
maxima={q:[0,0,0] for q in G}
last_l=last_ll=0
A,B,P,Q,C,Dw=[0]*6
def check(p,l,u,v,w):
    if p<=G[0]:return
    m=mult[bisect_left(edges,p)]
    # At a cell's upper limit the prefix is still the one after its left prime.
    for q,(z,zz) in clip.items():
        if p<=q:continue
        db=max(0,gb+w-P,Q-ga-max(last_ll,zz))
        assert db<S//10
        prod=db+ceildiv(db*db,2*(S-db))
        rec=max(0,w+mb-A,B-ma-max(last_ll,zz))
        wei=max(0,u-ba-C,Dw+bb-max(last_l,z))
        out=maxima[q]
        for i,x in enumerate((prod*u*m,rec*u*m,wei*m*S)):out[i]=max(out[i],x)
for p,l,u,v,w in logpair(primes(T)):
    check(p,l,u,v,w)
    a,b=S//p,ceildiv(S,p)
    x,y=series(p)
    A+=a; B+=b; P+=a+x; Q+=b+y
    C+=l//p; Dw+=ceildiv(u,p)
    last_l=l; last_ll=v
for p,l,u,v,w in logpair([T]): check(p,l,u,v,w)
for q,row in maxima.items():
    nums=[(I(z)/S**3).b for z in row]
    print('finite power scaled upper',q,*nums)

bound_rows=[(50000,'.0268','.0292'),(60000,'.0248','.0272'),
            (70000,'.019675','.0214'),(104000,'.019675','.019675')]
for q,product,weighted in bound_rows:
    v=[(I(z)/S**3).b for z in maxima[q]]
    assert max(v[:2])<D(product) and v[2]<D(weighted),(q,v)
print('finite power joins passed')
