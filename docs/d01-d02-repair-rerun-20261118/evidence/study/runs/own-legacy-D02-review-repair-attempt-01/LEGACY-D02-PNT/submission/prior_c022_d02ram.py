"""D02 Ramanujan whole-interval / whole-ray certificate."""
from d02screen import *
from collections import defaultdict

def ac(n):
    return sum(comb(n,j)*fac(j)-fac(j)*fac(n-j) for j in range(n+1))

@lru_cache(None)
def uu(l,N=17):
    x=I(l); P=sum(I(fac(j))/x**j for j in range(N+1))
    v=4*x*e(-x)+minI(I(fac(N+1))/x**N,
                       2*I(fac(N+1))/x**(N+1)+x*e(-x/2))
    return P,v

@lru_cache(None)
def mainerr(l,N=17):
    x=I(l); P,v=uu(l,N)
    assert x>N+1
    f=sum(1/(1-I(j)/(x-1)) for j in range(N+1))
    return (2*P+v)*v+x/(x-1)*f*e(2-x)

@lru_cache(None)
def square(N):
    s=defaultdict(int)
    for j in range(N+1):
        for k in range(N+1):
            if j+k>N: s[j+k]+=fac(j)*fac(k)
    return tuple(s.items())

def qerr(l,r,n=4,N=17):
    x=I(l); return I(r)**n*(mainerr(l,N)+sum(I(v)/x**k for k,v in square(N)))

def cpi(L):
    x=I(L)
    return A0*(1+1/(I('.9')*x))+117*e(-x/2)*(1+1/(I('.4')*x))+3*x*e(10-x)

@lru_cache(None)
def hsm(L,B=b):
    x=I(L); aa=I(20); A=1-B
    def j(t): return I('.04620')*e(-t/2)+2*e(-t)+I('7e-12')*e(-A*t)
    at=3*aa*e(10-aa)+j(aa)/aa
    return (at*x/aa*e(aa-x)+j(x)/x+I('3.04620')*e(-x/2)/(I('.4')*x)
            +I('7e-12')*e(-A*x)/((B-F(1,10))*x)+2*x*e(-x)/aa)

@lru_cache(None)
def spi(L,B=b,dusart_only=False):
    x=I(L)
    return screen(L,B,dusart_only,c=F(7,20))*e(-(1-B)*x)+3*e(-x/2)+hsm(L,B)

@lru_cache(None)
def d(l,r,B=b):
    x=I(l)
    C=cpi(l)
    if r<=58: C=minI(C,(x*x+2*x)*e(-x/2)/(8*PI)+1354*x*e(-x))
    if r<=F('43.7'): C=minI(C,e(-x/2)*(I('1.95')+I('3.9')/x+I('19.5')/x**2)+4*x*e(-x))
    if l>=58: C=minI(C,A0+117*e(-x/2)+hsm(l,B))
    if l>=t0: C=minI(C,spi(l,B))
    return C

@lru_cache(None)
def smallminus(l):
    x=I(l); U0=e(-x/2); V0=e(-2*x/3)
    j=I('.04620')*U0+2*e(-x)+I('7e-12')
    g=I('1.046200147')
    # Constants for the prefix to log=20, using log derivative from 10.
    prefix=(241+g*e(10)/(400*I('.3'))+I('1.78')*e(I(20)/3)/(400*(I(1)/3-I('.2'))))
    integ=(prefix*x*e(-x)+g*U0/(I('.4')*x)
             +I('1.78')*V0/((I(1)/3-I('.1'))*x)+2*x*e(-x)/10+I('7e-12')/(I('.8')*x))
    return I('1.751000147')*U0+I('1.78')*V0+j/x+integ

def loss(l,r,n=4,N=17,B=b,tail=False,shift=F(1),one=False):
    x=I(l)
    D1=spi(l-shift,B) if tail else d(l-shift,r-1,B)
    D2=spi(l,B) if tail else d(l,r,B)
    if r-1<=F(299,10) and l-shift>=20: D1=minI(D1,smallminus(l-shift))
    if one: D2=minI(D2,3*x*e(-x))
    P,v=uu(l,N)
    return I(r)**n*(x/(x-shift)*D1+(2*(P+v)+D2)*D2)

def polyr(r,n,N):
    return sum(I(ac(k))/I(r)**(k-n) for k in range(n,N+1))

def shiftcost(l,Beta):
    x=I(l); v=1+4/x**4
    return (Beta+14*v+4/x**3)/(1-v/x)

def cover(l,r,step,n=4,N=17,shifted=None,B=b,one=False):
    l,r,step=F(l),F(r),F(step)
    worst=None
    while l<r:
        u=min(r,l+step)
        s=F('1.001') if shifted is not None else F(1)
        v=polyr(u,n,N)-loss(l,u,n,N,B,False,s,one)-qerr(l,u,n,N)
        if shifted is not None: v-=shiftcost(l,shifted)
        if worst is None or v.lo<worst[0].lo: worst=(v,l)
        l=u
    return worst

def reserve(L,n,N=17,B=b,shifted=None):
    s=F('1.001') if shifted is not None else F(1)
    w=I(ac(n))-loss(L,L,n,N,B,True,s)-qerr(L,L,n,N)
    if shifted is not None: w-=shiftcost(L,shifted)
    assert L>n/(1-B)+s+2 and L>N
    return w


def strengthened_tail(L,n,N,k=0,B=b,kind=None):
    x=I(L)
    if kind is None:
        assert L>=t0+1 and L>N/(1-B)+3
        err=loss(L,L,n,N,B,True)
    else:
        assert L>=201 and L>n/(1-b)+20
        d1,d2=kind(L-1),kind(L)
        pp,v=uu(L,N)
        err=x**n*(x/(x-1)*d1+(2*(pp+v)+d2)*d2)
    return polyr(L,n,N)-I(k)-err-qerr(L,L,n,N)

def high_table():
    for n in range(7,41):
        N=max(17,n+5)
        def first(B):
            l=max(int(N/(1-B))+4,156); r=47*n
            assert strengthened_tail(r,n,N,B=B)>0
            while r-l>1:
                j=(l+r)//2
                if strengthened_tail(j,n,N,B=B)>0:r=j
                else:l=j
            assert strengthened_tail(r,n,N,B=B)>0
            assert strengthened_tail(r-1,n,N,B=B)<0
            return r
        aa,bb=first(b),first(F(7,8))
        alt=polyr(aa,n,N)-loss(aa,aa,n,N,F(7,8))-qerr(aa,aa,n,N)
        assert aa<bb and alt<0
        print(n-4,N,aa,bb,'fraction of next coefficient left:',strengthened_tail(aa,n,N)/ac(n), flush=True)

def direct(L):
    x=I(L)
    return (x*x+x/b)*e(-a*x)/64+3*e(-x/2)*(1+1/(I('.49')*x))+I('7e-15')*x/200*e(200-x)

def main():
    prelim()
    assert I('4.01')>e(log(2)/2)+I('1.000000147')+I('1.78')*e(-log(2)/6)
    assert log(2)>F(2,3)
    assert 241>4+2*I('4.01')*(I(10)*I(9)/4+e(5)/log(100)**2)+(I('.04620')*e(-5)+2*e(-10)+I('7e-12'))*e(10)/100
    assert e(1)>2 and e(F(299,10))<10**13 and e(F('30.8'))<10**19
    es=[('27.8','27.95','.01'),('27.95','28.24','.1'),('28.24','28.77','.25'),
        ('28.77','29.60','.5'),('29.60','30.45','.8'),('30.45','30.8','1')]
    for l,r,m in es:
        v,_=cover(l,r,'.002',one=True);assert v>I(m)
        print('early subinterval, lower margin',l,r,v,flush=True)
    for l,r,st,coeff in [(49,'49.5','.025',65),('49.5',58,'.025',83),
             (58,154,'.25',83),(154,167,'.025',83),(167,172,'.02',83)]:
        v,_=cover(l,r,st,6); assert v>I(coeff)
        print('second-coefficient segment, lower margin',l,r,v,flush=True)
    for l,k in [(172,83),('169.2',90),(173,110),(178,130),(183,140),('185.5',145)]:
        v=strengthened_tail(F(l),6,17,k)
        assert v>0,(l,k,v)
        print('second-coefficient whole tail, surplus',l,k,v,flush=True)
    for l,r,st in [(58,154,'.25'),(154,167,'.025'),(167,172,'.02')]:
        v,_=cover(l,r,st,6,shifted=68);assert v>1
        print('shifted interval, lower margin',l,r,v,flush=True)
    assert reserve(F(172),6,shifted=68)>1
    assert (1+I(13)/58+I(68)/58**2)<2
    assert 4/I(58)**4<I('.001')
    # Direct A branch, no density or inferred strip needed.
    # Use CH2 on the compact segment; the onset 49 joins via the 65 branch
    # finite proof and cancelation of the leading powers.
    for l,r,step in [(58,180,'.25'),(180,222,'.1')]:
        x=F(l)
        while x<F(r):
            y=min(F(r),x+F(step)); X=I(x); P,vv=uu(x)
            D1,D2=cpi(x-1),cpi(x)
            err=I(y)**5*(X/(X-1)*D1+(2*(P+vv)+D2)*D2)
            assert polyr(y,5,17)-err-qerr(x,y,5)>I('12.5')
            x=y
    assert A0/(I('.9')*200)+117*e(-100)/(I('.4')*200)+600*e(-190)<I('7e-15')
    assert strengthened_tail(F(222),5,17,'12.5',kind=direct)>0
    # Analytic arbitrarily high orders.
    for L,c in [(175,'.24'),(180,'.24'),(535,'.144')]:
        assert spi(F(L))*e(a*I(L))<I(c)
    assert I('.24')*(192*e(a)/191+I('2.04')+I('.24')*e(-192*a))<I('.79')
    assert I('.144')*(192*e(a)/191+I('2.04')+I('.144')*e(-192*a))<I('.47')
    assert 1+I(2)/192+2*(I(1)/16)**10+192*e(-96)+4*192*e(-192)<I('1.02')
    r=32*e(1-32*a);s=32*e(-15)
    assert r<1 and s<I('.5')
    assert 24*(I('.79')*r**6+5*32*6*s**6+I(10)/16**4)<1
    c=I('27.6443'); h0=4*log(20)+2
    assert c*20-h0>536 and (c-26)*20>h0 and c-26>I(4)/20
    assert log(c)+1-a*c<0 and 4*(a-1/c)<I('.5')
    assert I('.94')*e(2*(a-1/c))/e(log(2)/2)+20/I(16)**4+2*5*26*20*(26*e(-12))**20 < 1
    t=F(187)
    assert polyr(t,6,17)-loss(t,t,6,17,F(7,8))-qerr(t,t,6)<65
    print('B0 transition certificate does not supply K=65 at L=187',flush=True)
    high_table()

if __name__=='__main__': main()
