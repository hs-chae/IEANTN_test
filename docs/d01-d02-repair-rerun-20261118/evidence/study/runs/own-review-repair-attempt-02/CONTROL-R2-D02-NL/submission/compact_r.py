"""Compact strict Ramanujan joins using monotone *unscaled* costs."""
from second_r import *
from second_m import WIDER
from pathlib import Path

@lru_cache(None)
def jb(v,cap):
    u=I(v)
    E1=mini(
        *(I(sec(u,cap,h).r) for h in WIDER),
        sourcefloor+I('113.67')*ef(I('.5'),u))
    return mini(jbound(u,cap), E1+6*spec_simple_prim(u,cap)/u+17000*u*ef(1,u))

@lru_cache(None)
def cp(l,cap):
    u=I(l)
    pp=horner(MFS[:N+1],1/u)
    en=jb(l,cap)+remN(u)
    return u/(u-1)*(jb(l-1,cap)+powterm(u-1))+(2*pp+en)*en+horner(dNminus,1/u)

def margin_block(l,r,cap,k):
    u=I(r)
    return (horner(dNplus[k:],1/u)-u**k*cp(l,cap)).l

def check():
    ref={int(k):(int(m),D(t),D(u)) for a,k,m,t,u in
         (s.split() for s in Path(__file__).with_name('second_r_run.txt').read_text().splitlines()
          if s.startswith('full '))}
    stride=100
    for k in range(6,13):
        m,b,c=ref[k]
        for u,cap in [(b,basecap),(c,newcap)]:
            verify(u,cap,k,False)
            assert margin_new(u,cap,k,False).l>m
            lo=int(u*stride)
            for j in range(lo-1,lo-301,-1):
                if margin_block(D(j)/stride,D(j+1)/stride,cap,k)<=m:break
                lo=j
            print('full compact',k,cap,D(lo)/stride,u,flush=True)
    for u,k in [(190,6),(225,7),(250,8),(300,9)]:
        cap=basecap
        stop=D(u)+3
        verify(stop,cap,k,False)
        M=min(DD[k],margin_new(stop,cap,k,False).l)
        for j in range(u*stride,int(stop*stride)):
            M=min(M,margin_block(D(j)/stride,D(j+1)/stride,cap,k))
        m=int(M.to_integral_value(rounding=ROUND_FLOOR))
        assert M>m
        print('fixed compact',u,k,cap,m,flush=True)

if __name__=='__main__': check()
