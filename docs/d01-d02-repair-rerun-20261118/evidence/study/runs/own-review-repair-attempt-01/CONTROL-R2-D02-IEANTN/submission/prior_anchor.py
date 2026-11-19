#!/usr/bin/python3.10
from mertens import *
from pathlib import Path
N=2000000000
unit=2**62
p=Path(__file__).with_name('sieve_receipt.txt')
d={}
for line in p.read_text().splitlines():
    a=line.split()
    if a[0].endswith('-anchor'):
        d[a[0]]=I(I(Q(int(a[1]),unit)).a,I(Q(int(a[2]),unit)).b)
L0=I(N).log()
T=d['theta-anchor']/N-1
R=d['reciprocal-anchor']-T/L0
G=d['weighted-anchor']-T
up=[(I('.19'),Q(1,2),0)]
dn=[(I('1.791001'),Q(1,2),0),(I('1.78'),Q(2,3),0)]
def anch(l,u):
    v,w=I(l),I(u)
    negR=(-ev(dn,l)/v-(1/L0+1/L0**2)*im(dn,L0,w)).a
    posR=(-ev(up,u)/w-(1/w+1/w**2)*(im(up,L0,v) if v.a>=L0.b else I(0))).b
    negG=(-ev(dn,l)-im(dn,L0,w)).a
    posG=(-ev(up,u)-(im(up,L0,v) if v.a>=L0.b else I(0))).b
    br=R+I(negR,posR)
    bg=G+I(negG,posG)
    be=I(max(br.b,br.a.copy_negate()+D('0.00000000025')))
    return [(be.exp()-1)*w**3,I(max(br.b,br.a.copy_negate()))*w**3,I(max(bg.b,bg.a.copy_negate()))*w**2]
CHSM=[(I('0.000000315'),Q(0),0),(I(33),Q(1,2),0)]
def ws(v):
    t=I(v)
    return (2*CHSM[0][0]+33*(1+2/t)*(-t/2).exp())/t
def after(l,u):
    T=piecewise(l,u)
    if l>=58:return T
    v,w=I(l),I(u)
    tw,tl=tails(l);tl=tl/v
    if l<K:
        t=I(K)
        F=ev(A,l);F0=ev(A,K);J=im(A,l,K)
        U=F+J+F0+ev(CHSM,K)+tw
        W=(F/v)+(1/v+1/v**2)*J+F0/t+ws(K)+tl
    else:
        U=ev(CHSM,l)+tw
        W=ws(l)+tl
    return (mini(T[0],(W.exp()-1)*w**3),
            mini(T[1],W*w**3),mini(T[2],U*w**2))
def chk():
    pi=I('3.14159265358979323846','3.14159265358979323847')
    z=(I(10000000)/(2*pi)).log()
    assert (z*z/(2*pi)-z/(6*pi)).b<33
    assert (pi/9999999).b<D('.000000315')
    assert I(K).exp().a>D('1000000000')

    assert (I(1)-I('166.64')/I(Q(L0.a))**3-I('.791')).a>D('.19')
    l=Q(L0.a);u=Q('23.3')
    beta5=[D(0)]*3
    while l<u:
        r=min(u,l+Q(1,64))
        beta5=[max(x,y.b) for x,y in zip(beta5,anch(l,r))]
        l=r
    print('anchor bridge from x=2e9 through L=23.3',*[f'{x:.9E}' for x in beta5])
    assert all(z<D('.0223') for z in beta5)
    obs=[D(0)]*3
    for l,u in [(Q('23.3'),K),(K,Q(58)),(Q(58),Q(190)),(Q(190),Q(200))]:
        M=[D(0)]*3
        while l<u:
            r=min(u,l+Q(1,64))
            M=[max(v,x.b) for v,x in zip(M,after(l,r))]
            l=r
        print('followup through L=',u,*[f'{x:.9E}' for x in M])
        obs=[max(x,y) for x,y in zip(obs,M)]
    assert all(z<D('.0223') for z in obs)
if __name__=='__main__':chk()
