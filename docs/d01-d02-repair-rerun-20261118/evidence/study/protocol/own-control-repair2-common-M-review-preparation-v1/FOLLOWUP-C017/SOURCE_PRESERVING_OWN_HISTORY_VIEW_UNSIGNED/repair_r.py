"""Strict Ramanujan margins with a higher-order truncation and new spectral layer."""
from repair_spectral import *
from functools import lru_cache

N2=64
MFS=[factorial(j) for j in range(2*N2+1)]
DD=[sum(MFS[i]*comb(j,i) for i in range(min(N2,j)+1))
    -sum(MFS[i]*MFS[j-i] for i in range(max(0,j-N2),min(N2,j)+1))
    for j in range(2*N2+1)]
POS=[max(0,x) for x in DD]
NEG=[max(0,-x) for x in DD]
hh=128

def anchor():
    v=I(hh)
    residual=vintegral(v)-v.exp()/v*horner(MFS[:N2+1],1/v)
    assert 0<residual.l and residual.r<D('6e7')
    print('N64 anchor residual',residual)

def remainder(v):
    return 6*10**7*v*ef(1,v)+I(hh)/(hh-N2-2)*MFS[N2+1]/v**(N2+1)

def jbound(v,cap):
    return mini(spectral(v,cap),continuous_spectral(v,cap),sec(v,cap))+6*spec_simple_prim(v,cap)/v+17000*v*ef(1,v)

def cost(u,cap,high):
    assert u.l>=141
    nn=N2 if high else N
    pp=horner(MFS[:nn+1],1/u)
    en=jbound(u,cap)+(remainder(u) if high else remN(u))
    return u/(u-1)*(jbound(u-1,cap)+powterm(u-1))+(2*pp+en)*en+horner(NEG if high else dNminus,1/u)

@lru_cache(None)
def cachecost(u,cap,high):
    u=I(u)
    return cost(u,cap,high)

def margin_new(u,cap,k,high):
    return horner((POS if high else dNplus)[k:],1/I(u))-I(u)**k*cachecost(u,cap,high)

def verify(u,cap,k,high):
    # Analytic monotone ratio hypotheses; derivative enclosure at first point.
    a=1-I(cap)/800
    assert u>=141 and I(u-1).l>=((k+6)/a).r
    ds=DD if high else dN
    z=I(u)
    assert k+2<=(N2 if high else N)+1 and all(v>=0 for v in ds[:k+3])
    loss=sum((I(j-1)*max(0,ds[k+1+j])/z**j for j in range(2,len(ds)-k-1)),I())
    assert loss.r<ds[k+1]

def findray(k,cap,high,m):
    a=1-I(cap)/800
    start=max(1410,int((((k+6)/a+1)*10).r.to_integral_value(rounding=ROUND_CEILING)))
    stop=30000
    assert margin_new(D(stop)/10,cap,k,high).l>m
    while start<stop:
        p=(start+stop)//2
        if margin_new(D(p)/10,cap,k,high).l>m: stop=p
        else: start=p+1
    u=D(stop)/10
    verify(u,cap,k,high)
    assert margin_new(u,cap,k,high).l>m
    return u

EARLY_ROWS=[(4,'0','28.14'),(4,'.1','28.30'),(4,'.25','28.58'),
            (4,'.5','29.12'),(4,'.75','29.80'),(4,'.9','30.32'),
            (4,'1','30.74'),(5,'8','32.24'),(5,'10','44.92'),
            (5,'12','45.78'),(5,'14','47.04')]

def early_rows():
    # A local overlap with each already certified ray; each interval closed.
    j=5000
    for k,m,old in EARLY_ROWS:
        upper=int(D(old)*j)
        low=upper-400
        last=low
        for b in range(low,upper):
            u=I(D(b)/j,D(b+1)/j)
            if margin(u,basecap,k,fast=True).l<=D(m): last=b+1
        assert last<upper
        print('early',k,m,str(D(last)/j),old,flush=True)

if __name__=='__main__':
    anchor()
    assert DD[:4]==[0]*4 and all(x>0 for x in DD[4:N2+1])
    for k in range(6,63):
        print('full',k,DD[k],*(str(findray(k,cap,k>=30,DD[k])) for cap in (basecap,newcap)),flush=True)
    for u,k in [(190,6),(225,7),(250,8),(300,9)]:
        for cap in (basecap,newcap):
            verify(u,cap,k,False)
            w=margin_new(D(u),cap,k,False)
            m=min(DD[k],int(w.l.to_integral_value(rounding=ROUND_FLOOR)))
            assert w.l>m
            print('fixed',u,k,cap,m,flush=True)
    early_rows()
