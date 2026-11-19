
from density import *
from functools import lru_cache
# Conjugate-inclusive sum of inverse squares < .0503; above H < 5.8e-12.
from edge import lograt
def lowcert():
    u=F('14.13');total=0
    while u<280:
        v=min(u+F(1,4),280);r=v/F('6.283')
        n=(r*(lograt(r)[1]-1)+F(15,8)).__floor__()
        total+=2*n*(1/u**2-1/v**2);u=v
    total+=2/F('3.1415')*lograt(F(280)/F('6.283'))[1]/280+(2*(F(23,8)+F('.2')*lograt(F(280))[1])+F('.2'))/280**2
    assert total<F('.0503')
lowcert()
assert 2/F('3.125')*(j1-F('1.83'))/H+(2*(F(23,8)+F('.2')*j1)+F('.2'))/H**2<F('5.8e-12')
assert EL(F('.807'))*14<F('6.25') and EL(F('1.83'))*F('6.25')>1
assert EL(F('2.64'))*14<1 and EL(F('1.84'))*F('6.284')<1

LOW=F('.0503'); HIGH=F('5.8e-12'); G=F('1.84')
def Z(u,cap,w=0):
    cc=1-cap
    return (1+4/(H*u)*w)*HIGH*E(cc*u)+(1+4/(14*u)*w)*LOW*E(u/2)

def bp(u):return F('1.000102')*E(u/2)+F('2.67')*E(2*u/3)
def bm(u):return F('.999799')*EL(u/2)-F('1.78')*E(2*u/3)
def k(u):return (u+1)/u**2
def wpm(u):
    return ((F('2.000002')*E(u/2)+F('2.67')*E(2*u/3)),F('1.9998')*EL(u/2))
def em(u,a,b,order): # signed Dpow integral lower if needed
    return a*EL(u/2)-b*E(2*u/3)

@lru_cache(maxsize=20000)
def ep(u,cap,sgn=True):
    vs=minv(u,cap)
    if u>=100:vs=min(vs,val(u,discrete(cap)),val(u,discrete(cap,F(".80"))))
    l,h=-vs,vs
    if F(20)<=u<=F('29.9'):
        assert EL(F('29.9'))*10**13>1
        l=max(l,-F('.751')*E(u/2));h=min(h,F('.791')*E(u/2))
    if F('29.9')<=u<=58:
        p=val(u,P);pm=F('.9999')*EL(u/2)
        th=u*u*E(u/2)/25
        l=max(l,-th+pm);h=min(h,th+p)
    if u<=F('39.47') and sgn:h=min(h,val(u,P))
    if 34<=u<=58:
        b=(F('.0398')*u*u-F('.385')*u+F('5.80'))*E(u/2)
        l=max(l,-b);h=min(h,b)
    return l,h

# Suffix integral of prime powers has lower J >= coefficient exp(-L/2).
# For k use k(t) >= k(L) (L/t)^2 >= k(L) exp(-2(t-L)/L).
def powint(u,w):
    up,dn=wpm(u)
    if w:
        up*=k(u);dn*=k(u)/(1+4/u)
    return up,dn
def intervals(u,cap): # weighted, unweighted, log-product
    assert u>=20
    l,h=ep(u,cap)
    p,pm=val(u,P),F('.9999')*EL(u/2)
    result=[]
    for w in (0,1,2):
        isw=int(w>0); f=1/u if isw else 1; weight=k(u) if isw else 1
        z=Z(u,cap,isw)
        im,ip=-weight*(z+G*E(u)),weight*z
        C=E(u)/(2*(1-E(u))) if w==2 else 0
        pu,pl=powint(u,isw)
        bl=max(F(0),bm(u));bh=bp(u)
        if isw:bl=max(F(0),bl/u-2*bh/u**2);bh/=u
        if w==2:bl=max(0,bl-C)
        dl=l*f-ip+bl;dh=h*f-im+bh
        tl=l-p;th=h-pm
        if F('29.9')<=u<=58:
            t=u*u*E(u/2)/25
            tl=max(tl,-t);th=min(th,t)
        if u<=F('39.47'):th=min(th,0)
        dl=max(dl,tl*f-ip+pl-C)
        dh=min(dh,th*f-im+pu)
        result.append((dl,dh))
    return result

def absenv(ivs):
    (a,b),(c,d),(l,h)=ivs
    assert max(abs(l),abs(h))<1
    # inexpensive product enclosures; theorem envelope exponentiates exact endpoints.
    return max(-a,b),max(-c,d),max(h, -l/(1+l)),max(h/(1-h), -l)
def pars(u,cap):
    # each resulting coefficient is nonincreasing on u>=150.
    # pick among different branch types (without CH or direct hypothesis).
    c=1-cap;fac=EL(c*u)
    bw=bp(u)/fac;z=G*E(u)/fac
    i1=(HIGH+LOW*E((F(1,2)-c)*u))
    ik=(1+4/(H*u))*HIGH+(1+4/(14*u))*LOW*E((F(1,2)-c)*u)
    a=[]
    for J,Q in list(opts(cap))+[(100,discrete(cap)),(100,discrete(cap,F(".80")))]:
        if u<J or u<150 or any(m>(e-c)*u for b,m,e,M in Q):continue
        a.append(sum(b*u**m*E((e-c)*u)*(u/(u-M) if M else 1) for b,m,e,M in Q))
    b=min(a)
    W=b+i1+z+bw
    D=b+(1+1/u)*(ik+z)+bw
    return W,D,D/(1-D*E(c*u)/u)
if __name__=='__main__':
    for cap in (B0,B2):
        for j in [150,165,170,175,180,185,190,194,195,200,205,210,225,250,300,400,600,800,1000,1500,3000]:
            u=F(j)
            print(cap,j,'coefficients',*[float(a) for a in pars(u,cap)],'signed errors',*[float(a) for a in absenv(intervals(u,cap))])
