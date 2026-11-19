#!/usr/bin/python3.10
"""Outward-rounded certificate; no third-party modules. Run with mode ram, mertens, endpoint or all."""
from decimal import Decimal as Q, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from functools import lru_cache
from math import factorial, comb, isqrt
import sys

F=Context(prec=48,rounding=ROUND_FLOOR)
C=Context(prec=48,rounding=ROUND_CEILING)
N=Context(prec=48,rounding=ROUND_HALF_EVEN)
class I:
    __slots__=('l','r')
    def __init__(self,l,r=None):
        if isinstance(l,I): self.l,self.r=l.l,l.r; return
        self.l,self.r=Q(l),Q(l if r is None else r)
        assert self.l<=self.r
    def __add__(x,y):
        y=I(y); return I(F.add(x.l,y.l),C.add(x.r,y.r))
    __radd__=__add__
    def __neg__(x): return I(x.r.copy_negate(),x.l.copy_negate())
    def __sub__(x,y): return x+-I(y)
    def __rsub__(x,y): return I(y)+-x
    def __mul__(x,y):
        y=I(y)
        if x.l>=0 and y.l>=0: return I(F.multiply(x.l,y.l),C.multiply(x.r,y.r))
        if x.r<=0 and y.l>=0: return -((-x)*y)
        if y.r<=0 and x.l>=0: return -(x*(-y))
        ds=[(u,v) for u in (x.l,x.r) for v in (y.l,y.r)]
        return I(min(F.multiply(u,v) for u,v in ds),max(C.multiply(u,v) for u,v in ds))
    __rmul__=__mul__
    def __truediv__(x,y):
        y=I(y); assert not y.l<=0<=y.r
        return x*I(F.divide(Q(1),y.r),C.divide(Q(1),y.l))
    def __rtruediv__(x,y): return I(y)/x
    def __pow__(x,n):
        assert isinstance(n,int)
        if n<0: return 1/(x**(-n))
        out=I(1)
        while n:
            if n%2: out*=x
            n//=2
            if n: x*=x
        return out
    def exp(x):
        return I(N.next_minus(N.exp(x.l)),N.next_plus(N.exp(x.r)))
    def ln(x):
        assert x.l>0
        return I(N.next_minus(N.ln(x.l)),N.next_plus(N.ln(x.r)))
    def __repr__(x): return '['+str(x.l)+','+str(x.r)+']'
def imin(*xs): return I(min(x.l for x in xs),min(x.r for x in xs))
def upper(x): return I(x.r)
def assertlt(a,b):
    a,b=I(a),I(b); assert a.r<b.l,(a,b)
def atan1(n):
    # Alternating 1/n series; 100 terms.
    v=I(1)/n
    tot=sum((-1)**k*v**(2*k+1)/(2*k+1) for k in range(100))
    return I(tot.l,(tot+v**201/201).r)
PI=16*atan1(5)-4*atan1(239)
E=I(1).exp()
LN2=I(2).ln()
H=3000175332800
h=I(H).ln()
lam=PI/(H-1-PI/3)
cH=I('113.67')
rows=[(2400,'7.798','4.101'),(2560,'8.162','3.693'),(2592,'8.538','3.613'),(2624,'8.927','3.533'),(2656,'9.330','3.453'),(2688,'9.747','3.373'),(2720,'10.176','3.293'),(2752,'10.620','3.213'),(2784,'11.076','3.133')]
def B(i,order=4,force_row=None):
    s=I(i)/3200
    _,c,d=([r for r in rows if r[0]<=i][-1] if force_row is None else rows[force_row])
    a=(8*s-5)/3;q=5-2*s
    sm=term=I(1)
    for k in range(1,order+1):
        term*= (q-k+1)/(a*h);sm+=term
    return 2*(I(c)*(q*h.ln()-a*h).exp()/a*sm+I(d)*(h*h+2*h+2)/H)
BS=[]
for i in range(2400,2800):
    u=B(i).r
    BS.append(min(u,BS[-1]) if BS else u)
END=[2800,2700]
def spec(j):
    end=END[j];bs=BS[:end-2400]
    return [(1-I(i)/3200,I(u)-v) for i,u,v in zip(range(2401,end+1),bs,bs[1:]+[Q(0)]) if u!=v]
SPECT=[spec(j) for j in (0,1)]
# To evaluate across many cells, share one common power table per argument.
@lru_cache(maxsize=15000)
def ds(L):
    L=I(L); w=(-L/3200).exp()
    acc=I(0); head=I(0)
    x0=w**800
    for i in range(2400,2800):
        x0/=w
        v=(I(BS[i-2400])-BS[i-2399])*x0 if i<2799 else I(0)
        if i==2699: head=acc+BS[i-2400]*x0
        acc+=v
    base=Q('2.091')*L*(-L/3).exp()+L**2/16*(-L/4).exp()
    return base+acc+BS[-1]*x0,base+head

def A_C(L):
    L=I(L)
    return lam+ cH*(-L/2).exp()

def bC(L):
    L=I(L)
    return lam*(1+I(10)/9/L)+Q('114.671001')*(1+I('2.5')/L)*(-L/2).exp()+Q('1.78')*(1+I(30)/7/L)*(-2*L/3).exp()+3100*L*(-L).exp()
def dstar(L,j):
    L=I(L);a=I(1)/8 if j==0 else I(5)/32
    return Q('2.091')*L*(-L/3).exp()+L**2/16*(-a*L).exp()
def bD(L,j,fallback=False):
    L=I(L)
    return (dstar(L,j) if fallback else ds(L.l)[j])*(1+Q('1.63')/L)+Q('1.000001')*(1+Q('2.23')/L)*(-L/2).exp()+Q('1.78')*(1+Q('3.53')/L)*(-2*L/3).exp()+40000000*L*(-L).exp()
def bF(L):
    L=I(L)
    d=L*L/(8*PI)
    if L.l>=34:
        d=imin(d,((L-2*(L/(PI*E)).ln())**2-4)/(8*PI)+Q('1.000001')+Q('1.78')*(-L/6).exp())
    return (d+2*L/(8*PI))*(-L/2).exp()+1250*L*(-L).exp()
@lru_cache(maxsize=30000)
def ub(L,j,early,fallback=False):
    v=bC(L)
    if early: v=imin(v,bF(L))
    if L>=40: v=imin(v,bD(L,j,fallback))
    return upper(v)


def psi_bound(L,j,early):
    L=I(L)
    u=A_C(L)
    if early and L.l>=34:
        u=imin(u,((L-2*(L/(PI*E)).ln())**2-4)/(8*PI)*(-L/2).exp())
    if L.l>=40:
        u=imin(u,ds(L.l)[j])
    return u

@lru_cache(maxsize=30000)
def improved_parts(L,j,early):
    l=I(L)
    a=I(1)/8 if j==0 else I(5)/32
    J=(Q('.1645')*(-l/2).exp()+Q('8e-12')*(1+1/(Q('.9')-a))*(-a*l).exp()
        +Q('1.838')*(-l).exp()+(-3*l).exp())/l +3104*l*(-l).exp()
    drift=(Q('1.000001')*(1+Q('2.5')/l)*(-l/2).exp()
           +Q('1.78')*(1+I(30)/7/l)*(-2*l/3).exp())
    u=psi_bound(l,j,early)+J
    return u,u+drift

def two_errors(l,r,j):
    lo,hi=I(l),I(r)
    up,_=improved_parts(l,j,r<=58)
    _,dn=improved_parts(F.subtract(l,Q(1)),j,r<=59)
    pp=Q('.9999')*(-hi/2).exp()
    return (I(0,max(Q(0),imin(ub(l,j,r<=58),up-pp).r)),
            upper(imin(ub(F.subtract(l,Q(1)),j,r<=59),dn)))

cs=[sum(factorial(k)*comb(i,k) for k in range(min(20,i)+1))-sum(factorial(k)*factorial(i-k) for k in range(max(0,i-20),min(20,i)+1)) for i in range(4,41)]
def P(L):
    return sum(factorial(k)/L**k for k in range(21))
def err(L):
    return 10*L*(-L).exp()+I(15)*factorial(21)/4/L**21
def resmain(l,r,k):
    return sum(c/(r if c>=0 else l)**(i-k) for i,c in enumerate(cs[k:],k))
def loss(left,right,up,dn,k):
    z=up+err(left)
    return right**(4+k)*(left/(left-1)*dn+z*(2*P(left)+z))

def main_constants():
    c=(h-(2*PI).ln())
    assertlt((c*c-c/3)/(2*PI),cH)
    assertlt(599/LN2**2,1250)
    assertlt(1250+I(10).exp()/(4*PI),3100)
    assertlt(1250+I(20).exp()/(4*PI),40000000)
    assertlt(2*PI**2*I(29).exp()/58,H)
    assertlt(10**7,2*PI**2*I(17).exp()/34)
    assertlt(I(29).exp(),2*10**25)
    assertlt(I(58).exp(),2169*10**22)
    assertlt(I(40).exp(),2169*10**22)
    # arithmetical constants for FKS Lemma 2.1 at T0=100
    t=I(100).ln()
    r=Q('.137')*t+Q('.443')*t.ln()+Q('1.588')
    assertlt(1/(2*PI)+(Q('.137')*t+Q('.443'))/(100*t*(I(100)/(2*PI)).ln()),Q('.17'))
    assertlt(2*(I('.5922435112')+2*r/100),Q('1.4'))
    assertlt((10/(2*PI)).ln(),Q('.5'))
    assertlt(I('2.45').ln(),1)
    # F(exp(30)) by convergent elementary series, tail < 10^-50.
    def se(v):
        a=I(1);s=I(0)
        for n in range(1,181):
            a=a*v/n;s+=a/n
        return s
    a=I(30)
    val=2/LN2+(a/LN2).ln()+se(a)-se(LN2)+I('-1e-50','1e-50')-a.exp()/a*P(a)
    # tail at 30: use geometric ratio < 1/6 after n=180 (ratio 30/181).
    assertlt(I(30)**181/I(factorial(181))/181*I(6)/5,Q('1e-50'))
    assertlt(0,val); assertlt(val,10)
    print('main constants OK, anchor',val,flush=True)

# (coefficient index k, target, log onset B0, log onset B1)
ROWS=[
 (0,'0','39.25','39.25'),(0,'.25','39.8','39.8'),(0,'.5','40.5','40.5'),
 (0,'.75','41.4','41.4'),(0,'.9','42.1','42.1'),(0,'1','42.75','42.75'),
 (1,'10','45.2','45.2'),(1,'13','46.6','46.6'),(1,'14','47.25','47.25'),
 (2,'7.8','47.5','47.5'),(2,'75','196','48.9'),(2,'80','196.65','49.05'),
 (2,'100','200','171.8'),(2,'130','208.65','178.35'),(2,'140','214.9','182.8'),
 (2,'145','220.55','186.7'),(3,'1300','242.65','203.5'),
 (3,'1400','251.8','209.95'),(3,'1412','253.75','211.25'),
 (4,'10000','265.9','220.6'),(4,'13000','277.1','229.05'),
 (4,'13985','288','236.6'),(5,'100000','299.35','245.45'),
 (5,'140000','315.4','257.45'),(5,'145450','322.85','262.5'),
 (6,'1000000','332.5','270'),(6,'1600000','356.5','287.7'),
]
# Fixed-onset comparison (k, onset, B0 margin, B1 margin).
FIXED=[(2,'50','7.8','80'),(2,'170','7.8','86.7'),(2,'180','7.8','134.5'),
       (2,'190','14.9','145'),(2,'200','100.6','145'),
       (3,'211.25','-2100','1412'),(4,'237','-56066','13985')]

def ram():
    A=Q('450')
    def verify(k,m,a,j,improved=False,fallback=False):
        a,m=Q(a),Q(m)
        d=k+(m==cs[k])
        t=I(A)
        assert d+6 < (A-1)/8
        assertlt(loss(t,t,bD(A,j,fallback),bD(A-1,j,fallback),d)+sum(-c/t**(i-d) for i,c in enumerate(cs) if c<0),
                 cs[d]-(0 if d>k else m))
        if a>=A:return
        cells=0
        def part(l,r):
            nonlocal cells
            p,q=I(l),I(r)
            if improved:
                up,dn=two_errors(l,r,j)
            else:
                up,dn=ub(l,j,r<=58,fallback),ub(F.subtract(l,Q(1)),j,r<=59,fallback)
            lower=resmain(p,q,k)-loss(p,q,up,dn,k)
            if lower.l>m:
                cells+=1;return
            assert r-l>Q('.000001'),(l,r,k,j,m,lower)
            mid=N.divide(N.add(l,r),Q(2))
            part(l,mid);part(mid,r)
        ends=[a]+[Q(t) for t in [34,35,40,41,58,59,80,125,166,169,189,190,230,300,375] if a<t<A]+[A]
        for l,r in zip(ends,ends[1:]): part(l,r)
        return cells
    for k,m,a,b in ROWS:
        t0=verify(k,m,a,0);t1=verify(k,m,b,1)
        print('onset',k,m,a,b,t0,t1,flush=True)
    for k,a,m0,m1 in FIXED:
        print('fixed',k,a,m0,m1,verify(k,m0,a,0),verify(k,m1,a,1),flush=True)


    IMPROVED=[
       (0,'0','39.15','39.15'),(0,'.16','39.32','39.32'),(0,'1','42.6','42.6'),
       (2,'8.6','48','48'),(2,'80.7','197','49'),
       (3,'1412','253.65','211.11'),
       (4,'13985','287.93','236.52'),
       (5,'145450','322.85','262.45'),
    ]
    for k,m,a,b in IMPROVED:
        print('refined',k,m,a,b,verify(k,m,a,0,True),verify(k,m,b,1,True),flush=True)

    for k,m,a,b in [(0,'0','39.25','39.25'),(1,'7','46.6','46.6'),
                    (2,'145','360','275'),(3,'1412','405','326')]:
        print('fallback',k,m,a,b,verify(k,m,a,0,False,True),verify(k,m,b,1,False,True),flush=True)

def signed_bridge():
    # At x up to 1.2e17 the Dudek--Platt proof gives pi(x) < li(x) < F(x).
    # The constants of both li normalizations used by the corpus are below F.
    top=I(120*10**15).ln()
    B=top.r
    def check(a,m):
        def part(l,r):
            p,q=I(l),I(r)
            _,d=two_errors(l,r,0)
            out=resmain(p,q,0)-loss(p,q,I(0),d,0)
            if out.l>Q(m):return 1
            assert r-l>Q('.000001'),(l,r,m,out)
            mid=N.divide(N.add(l,r),Q(2))
            return part(l,mid)+part(mid,r)
        print('signed bridge',a,m,part(Q(a),B),flush=True)
    for a,m in [('36.55','0'),('36.64','.05'),('36.75','.1'),
                ('36.88','.16'),('36.98','.2'),('39','.8')]:
        check(a,m)
    assertlt(I('39.32'),top)
    assertlt(I('36.55').exp(),115*10**14)

def pi_count(n):
    m=isqrt(n)
    v=list(dict.fromkeys(n//i for i in range(1,m+1)))
    v+=list(range(min(m,v[-1]-1),0,-1))
    s={u:u-1 for u in v}
    for p in range(2,m+1):
        b=s[p-1]
        if s[p]==b: continue
        for u in v:
            if u<p*p: break
            s[u]-=s[u//p]-b
    return s[n]

def endpoint():
    n=38358837682
    a,b=I(n)/E,I(n+1)/E
    assert int(a.l)==int(b.r)==14111427770
    p,q=pi_count(n),pi_count(int(a.l))
    assert (p,q)==(1644673232,632207037)
    def gap(x):
        return E*x/x.ln()*q-p*p
    assertlt(gap(I(n)),0)
    l,r=I('38358837682.217926'),I('38358837682.217927')
    assertlt(gap(l),0);assertlt(0,gap(r))
    print('endpoint',p,q,gap(I(n)),l,r,flush=True)


def lastnot(k,L,m,j=0):
    L=I(L);p=L.l
    def B(p):
        return imin(bC(p),bD(p,j))
    g=resmain(L,L,k)-loss(L,L,B(p),B(p-Q(1)),k)
    assertlt(g,Q(m))
    print('not certified by this profile at',k,L,m,j,flush=True)

def kvals(L,j):
    L=I(L);a=I(1)/8 if j==0 else I(5)/32
    return [(I('.047'),I(1)/2),(I('8e-12'),a),(I('1.838'),I(1)),(I(1),I(3))]
def ktail(L,j):
    L=I(L)
    v=[(c*(-a*L).exp(),a) for c,a in kvals(L,j)]
    return sum(c for c,a in v),sum(c/a for c,a in v)

def pp_check(a):
    L=I(a);delta=I('3.965')*4/L**2
    rest=Q('1.000081')*I('1.5')*(1+1/L)*(
        sum((-(I(1)/2-I(1)/m)*L).exp() for m in range(3,8))
        +L/LN2*(-3*L/8).exp())+Q('6.002')*(-L/2).exp()
    return 1+delta*(3+2/L)+rest

def mux(L,j,d,corr):
    # Two explicit whole-domain bounds: weighted prime sum and common
    # log-envelope for products and prime reciprocals.
    L=I(L)
    K,J=ktail(L,j)
    p=Q(corr)*(-L/2).exp()
    return d+K+p, (d+(1+1/L)*K+(1/L+2/L**2)*J+p)/L

def den_limit(L,j):
    # For all U>=L, exp(a*U) times the two scaled bounds of mux
    # are nonincreasing (L>=170). For products apply expm1 <= z/(1-z).
    L=I(L)
    a=I(1)/8 if j==0 else I(5)/32
    d=ds(L.l)[j]
    v,w=mux(L,j,d,'1.34')
    return v*(a*L).exp(), L*w*(a*L).exp(),L*w*(a*L).exp()/(1-w)

def phi_early(L):
    # CH at least 1e7: chosen independent parameter on the full ray after e^29.
    L=I(L);T=I(10000000)
    t=(T/(2*PI)).ln(); ct=(t*t-t/3)/(2*PI)
    return PI/(T-1)+PI**2/(3*T**2)+ct*(-L/2).exp()

# fixed logarithmic onsets; coefficients for log-envelope and relative
# product envelope (and prime reciprocals), and weighted prime sums
# use the printed upper values if incorporating additional rows.
def mertens():
    assertlt(4*(h+1)/(5*H),Q('8e-12'))
    assertlt((2*PI).ln(),Q('1.838'))
    # prove N(u) <= u log(u)/5 for u>=100 using FKS Lemma 2.1 with Rosser constants
    u=I(100); R=Q('.137')*u.ln()+Q('.443')*(u.ln()).ln()+Q('1.588')
    assertlt(I(7)/8+R,u*u.ln()*(I(1)/5-1/(2*PI)))
    # RHS / u increases and (7/8+R(u))/u decreases on this ray.
    # Euler gamma enclosure from H_n-log n and the elementary integral test.
    n=10000; gamma=sum(I(1)/k for k in range(1,n+1))-I(n).ln()
    gamma=I((gamma-I(1)/n).l,gamma.r)
    assertlt(2+gamma-(4*PI).ln(),Q('.047'))
    assertlt(pp_check(18),Q('1.34'))
    assertlt(pp_check('17.8'),Q('1.37'))
    # Signed square-tail improvements on the finite CH2 Lemma 9.2 interval.
    assertlt(I('20.8').exp(),10**13)
    assertlt(32321,I('10.4').exp())
    assertlt(I('8e-12')*(I(30)*3/8).exp()+Q('1.838')*(-I(9)).exp()+(-I(45)).exp()+Q('.047'),Q('.048'))
    assertlt(I('64e-12')*(I(30)*3/8).exp()+Q('1.838')*(-I(9)).exp()+(-I(45)).exp()/3+Q('.094'),Q('.096'))
    assertlt(Q('.054'),1-I('3.965')*12/18**2-Q('.751')-Q('.048'))
    U=I('20.8')
    assertlt(Q('.06'),1-2/U-80/U**3*(3+2/U)-U*(-U/2).exp()
                      -Q('.751')-(1+1/U)*Q('.048')-(1/U+2/U**2)*Q('.096'))
    print('power correction beta',pp_check(18),pp_check('17.8'),flush=True)
    print('density crossover evidence',flush=True)
    for j,a,b in [(0,'189.023','189.024'),(1,'168.795','168.798')]:
        assertlt(A_C(a),ds(Q(a))[j])
        assertlt(ds(Q(b))[j],A_C(b))
        print(j,a,b,flush=True)
    assertlt(den_limit(200,1)[2],Q('.3'))
    for j in (0,1):
        k,_=ktail(20,j)
        assertlt(I(20).exp()*k/400+Q('1.838')/20+(-I(40)).exp()/800,4)
    # Check the strict comparison at the certified onset,
    # including ample allowance for prime powers and both integrations.
    l=I('168.82')
    v,w=mux(l,1,ds(l.l)[1],'1.34')
    assertlt(l*w/(1-w),Q('1.045e-12'))
    assertlt(l*w/(1-w),Q('.01')*(-l/8).exp())
    uu,_=improved_parts(l.l,1,False)
    assertlt(uu,Q('1.045e-12'))
    assertlt(uu,Q('.01')*(-l/8).exp())
    assertlt(Q('1.045e-12'),Q('1.046e-12')-(3*(-l/2).exp()))
    assertlt(Q('.01')*(-l/8).exp(),Q('.0104')*(-l/8).exp()-(3*(-l/2).exp()))
    assertlt(Q('1.046e-12'),PI/H-I(4)/(H*H))
    assertlt(Q('.0104'),I(BS[-1]))
    for i,end in enumerate([2560,2592,2624,2656,2688,2720,2752,2784,2800]):
        assertlt(Q('.0104'),B(end,3,i))
    for a in [170,175,180,185,190,200,225,250,300,400,500,600,800,1000,1500,2500,5000,10000]:
        print('power limits',a,[tuple(str(x.r) for x in den_limit(a,j)) for j in (0,1)],flush=True)
    for j in (0,1):
        u=I(300);a=I(1)/8 if j==0 else I(5)/32
        xx,zz=mux(u,j,dstar(u,j),'1.34')
        assertlt(xx*(a*u).exp()/u**2,Q('.0626'))
        assertlt(zz*(a*u).exp()/u/(1-zz),Q('.0626'))
    for i,c in [(2800,'.010444096'),(2700,'.146302424')]:
        assertlt(B(i),Q(c))
    for L,c0,c1 in [(170,'.021014','.295890'),(175,'.020438','.287504'),
       (180,'.019923','.280038'),(185,'.019459','.273345'),(190,'.019041','.267310'),
       (200,'.018312','.256857'),(225,'.016947','.237375'),(250,'.015996','.223871'),
       (300,'.014759','.206366'),(400,'.013463','.188160'),(500,'.012790','.178806'),
       (600,'.012377','.173108'),(800,'.011893','.166482'),(1000,'.011616','.162708')]:
        assertlt(den_limit(L,0)[2],Q(c0));assertlt(den_limit(L,1)[2],Q(c1))
        assertlt(Q(c1)*(-I(L)/32).exp(),Q(c0))
    assertlt(Q('.295890')*(-I(170)/32).exp(),Q('.002'))
    assertlt(I(10**13).ln(),30)
    assertlt(29,I(10**13).ln())
    # Compact-domain cover for log-safe early power-of-log inequalities.
    # Finite computational Lemma 9.2 is used only through x=10^13.
    earlyrows=[('17.8','.1','1.37'),('19.5','.05','1.34'),('22','.02','1.34'),
               ('24','.01','1.34'),('32','.005','1.34'),('37','.001','1.34'),
               ('46','.0001','1.34')]
    Y=I(10**13).ln()
    def early(k,c,z):
        k,c=Q(k),Q(c);s=Q(0);cells=0
        def part(l,r):
            p,q=I(l),I(r)
            if r<=Y.l:
                d=Q('.791')*(-p/2).exp()
            else:
                assert l>=29
                d=A_C(l)
            if l>=29:
                d=imin(d,phi_early(l),A_C(l))
            u,v=mux(p,0,d,z)
            if max((q*q*u).r,(q**3*v/(1-v)).r)<c:
                return 1
            assert r-l>Q('.000001'),(k,c,l,r,u,v)
            mid=N.divide(N.add(l,r),Q(2))
            return part(l,mid)+part(mid,r)
        ends=[k]+[m for m in [Q(29),Y.l,Q(30),Q(60),Q(100),Q(190),Q(220)] if k<m]
        for l,r in zip(ends,ends[1:]):cells+=part(l,r)
        t=I(220);d=ds(t.l)[0];u,v=mux(t,0,d,z)
        assertlt(t*t*u,c);assertlt(t**3*v/(1-v),c)
        print('early',k,c,cells,flush=True)
    for a,b,c in earlyrows: early(a,b,c)
if __name__=='__main__':
    m=sys.argv[1] if len(sys.argv)>1 else 'all'
    if m in ('all','ram','mertens'):main_constants()
    if m in ('all','ram'):ram();signed_bridge()
    if m in ('all','endpoint'):endpoint()
    if m in ('all','mertens'):mertens()
    if m in ('all','ram'):
        for k,x,m0 in [(2,'189.04','8'),(2,'199.8','100'),(2,'214.7','140'),
                         (2,'220.4','145'),(3,'253.6','1412'),(4,'287.8','13985'),
                         (5,'322.7','145450'),(6,'356.3','1600000')]:
            lastnot(k,x,m0)
