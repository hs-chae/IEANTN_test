"""Directed calculations for signed pi radii, margins and real onsets."""
from D01_check import I, F, exp, log, lt, less, approx, rng, LN2, PI, r0, TS, AT, BT, fac, ceil
from power import c, Q, J
from functools import lru_cache

a=I('1.048e-12')
B=I('115.1')
v=24
N=14
P=lambda t:sum(fac(j)/t**j for j in range(N+1))
C=fac(N+1)*4 # inflation over the derivative requirement 3*15!
Clo=I(0)

def li2(t):
    s=log(t/LN2)
    a=b=I(1)
    for j in range(1,121):
        a=a*t/j; b=b*LN2/j
        s+=(a-b)/j
    return s+I(0,ceil(10**60,10**32))
    # valid here only at t=24; explicit tail test in anchor().

def anchor():
    assert F(2*v**121,121*fac(121))<F('1e-32')
    t=I(v)
    lv=exp(-t)*t*li2(t)
    less(P(t)-Clo*t,lv)
    less(lv,P(t)+C/t**(N+1))
    less(exp(I('43.749')),10**19)
    less(PI/I(3000175332800),'1.048e-12')

def rr(t,j,up):
    # r0's prefix bounds 100000,100 are reused, but sharp integrals
    # after the pivot 16 give coefficients 8/7 and 8/3.
    p,b=AT[j],BT[j]+I('-.9999' if up else '1.4262')
    return p*(1+I(F(8,7))/t)+b*(1+I(F(8,3))/t)*exp(-t/2)+(100000*p+100*b+50)*t*exp(-t)

def plat(t,b=Q):
    y=I('186.09' if b==Q else '167.96')
    k=1-b
    z=I(max(0,(t-y).a),max(0,(t-y).b))
    return a*exp(-k*z)

def rd(t,b):
    # use plateau with log-ratio rate k; spectral density needed only at anchor
    return B*(1+I(F(8,3))/t)*exp(-t/2)+plat(t,b)*(1+I(F(7,5))/t)+(100000*a+100*B+3)*t*exp(-t)

def which(t,z,up,b):
    # The optimal bound for a cell is chosen by comparing worst endpoints.
    terms=[rr(t,j,up) for j in range(len(TS))]
    if up and z.b<=I('43.749').a:
        terms.append(2*t*exp(-t)) # sign to 10^19, finite RH paper §3.3 p.5
    if b is not None:
        terms.append(rd(t,b))
    return min(terms,key=lambda z:z.b)

from math import comb
bb=[sum(fac(j)*fac(n-j) for j in range(max(0,n-N),min(N,n)+1)) for n in range(2*N+1)]
aa=[sum(fac(j)*comb(n,j) for j in range(min(N,n)+1)) for n in range(2*N+1)]
dd=[x-y for x,y in zip(aa,bb)]
assert dd[:9]==[0,0,0,0,1,14,145,1412,13985]

def lower(t):
    return sum(dd[n]/t**(n-4) for n in range(4,2*N+1))
def losses(t,up,lo):
    return (2*P(t)+C/t**(N+1)+up)*(C/t**(N-3)+t**4*up)+Clo*t**5*exp(v+1-t)+t**5/(t-1)*lo
def gap(t,b=Q,strip_prefix=4):
    # bound t^(strip_prefix-4) times the normalized gap after subtracting
    # terms dd[4] through dd[strip_prefix-1]
    u=which(t,t,True,b); l=which(t-1,t-1,False,b)
    return sum(dd[n]/t**(n-strip_prefix) for n in range(strip_prefix,2*N+1))-t**(strip_prefix-4)*losses(t,u,l)

def verify_common():
    anchor()
    for b,y in [(Q,I('186.09')),(J,I('167.96'))]:
        less(c(y,b)*exp(-(1-b)*y),a)
    t=I('36.5')
    less(2*P(t)+C/t**(N+1)+rr(t,2,True),'2.07')

def finite(l,u,k,w,ray,b,step=4):
    l=F(l); u=F(u); step=F(step)
    k=int(k); w=F(w)
    count=0
    def cover(l,r):
        nonlocal count
        if l<F('43.749')<r:
            cover(l,F('43.749')); cover(F('43.749'),r); return
        f=gap(rng(l,r),b,k)-w
        if f.a>0:
            count+=1; return
        if r-l<=F(1,2048):
            raise ValueError(('finite',l,r,k,w,b,approx(f)))
        m=(l+r)/2
        cover(l,m); cover(m,r)
    start=l
    while l<u:
        r=min(u,l+step)
        cover(l,r)
        l=r
    if ray:
        # Pay for all negative coefficients and all errors with the first
        # strictly positive subsequent coefficient. See ram-new.md.
        t=I(u)
        cost=losses(t,rd(t,b),rd(t-1,b))
        j=k if w<dd[k] else k+1
        pay=dd[j]-w if j==k else dd[j]
        less(t**(j-4)*cost+sum((-dd[n])/t**(n-j) for n in range(j+1,2*N+1) if dd[n]<0),pay)
        assert all(dd[n]>=0 for n in range(k,j+1))
        assert u>=300 and u-1>=8*(j+2) and j<N+1
    print('gap passed',k,str(w),str(b),str(start),str(u),ray,count,flush=True)

base=[
    ('36.88',4,'.05',300), ('36.96',4,'.09',300), ('37',4,'.11',300),
    ('38',4,'.50',300), ('40.23',4,1,300),
    ('41.25',5,5,300), ('45',5,'9.7',300),
    ('46.8',5,'13.4',300), ('47.25',5,14,300),
    ('47.25',6,1,300), ('47.65',6,'20.5',300),
    ('190',6,49,300), ('200',6,112,300), ('210',6,136,300), ('219',6,145,300),
    ('220',7,190,350), ('240',7,1270,350), ('253',7,1412,350),
    ('289',8,13985,400), ('324',9,145450,500),
    ('350',10,1500000,510), ('360',10,1610021,510), ('397',11,19063832,550),
    ('432',12,241691425,600), ('480',13,3277187246,650),
]
sensitivity=[
    ('48',6,40,300), ('48.75',6,70,300), ('49',6,80,300), ('50',6,'82.4',300),
    ('176',6,124,300), ('186.6',6,145,300), ('190',7,500,350),
    ('212',7,1412,350), ('238.1',8,13985,400), ('267',9,145450,500),
    ('303',10,1610021,510), ('322',11,19063832,550), ('350',12,241691425,600),
    ('385',13,3277187246,650),
]

if __name__=='__main__':
    import sys
    verify_common()
    group=sys.argv[1] if len(sys.argv)>1 else 'base'
    if group=='base':
        for l,k,w,u in base: finite(l,u,k,w,True,Q)
        finite('36.88','754',4,0,False,None)
    elif group=='sensitivity':
        for l,k,w,u in sensitivity: finite(l,u,k,w,True,J)
    else:
        raise ValueError(group)
