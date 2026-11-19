"""Exact rational certificates for the analytic Ramanujan bounds."""
from fractions import Fraction as Q
from math import factorial as fac, comb
from functools import lru_cache
from pathlib import Path
from d01_cert import bracket

eL=Q(2718281828459045235,10**18)
eU=eL+Q(1,10**18)
c=Q(397888,10**7)
q=Q('1.047198e-12')
def series(t,n):
    s=v=Q(1)
    for i in range(1,n+1):
        v=v*t/i
        s+=v
    return s,s+v*t/(n+1)/(1-t/(n+2))
assert series(Q(1),25)[0]>eL and series(Q(1),25)[1]<eU

@lru_cache(None)
def expb(t):
    t=Q(t)
    if t<0:
        l,r=expb(-t)
        return 1/r,1/l
    m=t//1
    l,r=series(t-m,18)
    return eL**m*l,eU**m*r
@lru_cache(None)
def eu(t):
    s=10**90
    if t<=-210:
        assert eL**210>s
        return Q(1,s)
    return Q((s*expb(t)[1]).__ceil__(),s)
def el(t):return expb(t)[0]

def logb(x):
    assert x>=1
    k=0
    while x>=2:
        k+=1;x/=2
    def at(t):
        z=(t-1)/(t+1)
        s=2*sum(z**(2*j+1)/(2*j+1) for j in range(50))
        return s,s+2*z**101/(101*(1-z*z))
    a,b=at(Q(2))
    g,h=at(x)
    return k*a+g,k*b+h

def alt(t,n):
    v=sum((-1)**j*t**(2*j+1)/(2*j+1) for j in range(n))
    w=v+(-1)**n*t**(2*n+1)/(2*n+1)
    return min(v,w),max(v,w)
# Machin's formula follows by the tangent addition law in the first quadrant.
pl=16*alt(Q(1,5),12)[0]-4*alt(Q(1,239),6)[1]
pu=16*alt(Q(1,5),12)[1]-4*alt(Q(1,239),6)[0]
assert 1/(8*pl)<c and pu/(3*10**12)<q
def H(u):return sum(Q(fac(i))/u**i for i in range(21))
def V(u):
    v=4*u*eu(-u)+12*Q(fac(21))/u**21
    if u>=40:
        v=min(v,1000*u*eu(-u)+Q(20,9)*fac(21)/u**21)
    return v
def h0(u):return q+117*eu(-u/2)
def m0(u):return (q*20/19+260*eu(-u/2))/u+Q(16,5)*u*eu(20-u)
def li_anchor():
    u=Q(24); n=120
    s=sum(u**k/Q(k*fac(k)) for k in range(1,n+1))
    t=u**(n+1)/Q((n+1)*fac(n+1))/(1-u/(n+2))
    l,r=logb(u)
    assert s+l-eu(u)*H(u)/u>0
    assert s+t+r+1-el(u)*H(u)/u<4

S=[sum(fac(i)*fac(k-i) for i in range(max(0,k-20),min(k,20)+1))
   for k in range(41)]
C=[sum(comb(k,j)*fac(j) for j in range(k+1))-S[k] for k in range(21)]
assert C[:7]==[0,0,0,0,1,14,145] and min(C[4:])>0
def mainlower(a,b):
    return (sum(Q(C[k])*b**(4-k) for k in range(4,21))
           -sum(Q(S[k])*a**(4-k) for k in range(21,41)))

# All proof arithmetic is rational; float routine below is diagnostics only.
A0=Q('43.7')
P=Q('.01955')
AC=Q('29.9')
def short(t):
    return (Q('1.95')+Q('3.9')/t+Q('19.5')/t**2)*eu(-t/2)+2*t*eu(-t)
def chlow(t):
    return Q('1.84')*(1+Q(18,7)/t)*eu(-t/2)+Q('2.04')*(t/18)*eu(9-t)
def mstar(t):
    return (7*eu(-t/2)/t + Q('8e-12')*eu(-t/8)/t + Q('3.21')*t*eu(20-t))
def hi(t,p=P):
    return p*eu(-t/8)+mstar(t)
WTS=[(Q(int(a),10000),Q(int(b),10**6)) for a,b in (
       r.split() for r in Path(__file__).with_name('d01_weights.txt').read_text().splitlines())]
@lru_cache(None)
def theta_coeff(L):
    assert L>=190
    bulk=((L/3+1)**2/6+2)*eu(-Q('.175')*L)+Q('2.091')*L*eu(-Q(5,24)*L)
    p=bulk+WTS[-1][1]+sum((u-v)*eu((t-Q('.875'))*L)
                          for (s,u),(t,v) in zip(WTS,WTS[1:]))
    return p+Q('1.000000147')*eu(-3*L/8)+Q('1.78')*eu(-Q(13,24)*L)
@lru_cache(None)
def wt_refined(fine=False):
    dscale=10**12
    l,u=logb(Q(3*10**12))
    y,Y=Q((l*dscale).__floor__(),dscale),Q((u*dscale).__ceil__(),dscale)
    ly=Q((logb(Y)[1]*dscale).__ceil__(),dscale)
    splits=[s for s,w in WTS]+[Q(j,100000) for j in range(87491,87500)]
    if fine:
        splits += [Q(j,10**6) for j in range(874991,875000)]
        splits += [Q(j,10**7) for j in range(8749991,8750000)]
    v=[]
    for s in splits:
        c,d=bracket(s); r=(8*s-5)/3; q=5-2*s; assert 3<q<4
        pol=Q(0); f=Q(1)
        for j in range(5):
            pol+=f/(r**(1+j)*y**j)
            f*=q-j
        u=2*(c*eu(-r*y)*eu(q*ly)*pol+d/(3*10**12)*(Y*Y+2*Y+2))
        u=Q((10**8*u).__ceil__(),10**8)
        v.append((s,min(u,v[-1][1]) if v else u))
    assert v[-1][1]<Q('.010454')
    return v
@lru_cache(None)
def psi_new(L,fine=False):
    assert L>=40
    # One directed enclosure of F*(L) + the Dusart prime-power correction.
    W=wt_refined(fine)
    bulk=((L/3+1)**2/6+2)*eu(-Q('.175')*L)+Q('2.091')*L*eu(-Q(5,24)*L)
    f=bulk+W[-1][1]+sum((u-v)*eu((t-Q('.875'))*L)
                          for (s,u),(t,v) in zip(W,W[1:]))
    return f
def theta_new(L):
    return psi_new(L)+Q('1.000000147')*eu(-3*L/8)+Q('1.78')*eu(-Q(13,24)*L)
def smooth(t):
    return (123*(1+Q(20,9)/t)*eu(-t/2)
           +Q('3.6e-6')*(1+1/(t*(Q(19,20)-Q(1,16))))*eu(-t/16)
           +Q(16,5)*t*eu(20-t))
def anchored(t):
    # Anchor at 40; Schoenfeld only used on [40,t], not extended beyond.
    return c*(t**2+2*t)*eu(-t/2)+Q(16,5)*t*eu(20-t)
# Re-anchor at s=29.9; see finite_anchor.md.
s0=AC
def conv(a):
    return (Q('.155')*eu(-a/2)+Q('7.2e-12')*eu(-a/8))/a+Q('.074')*a*eu(s0/2-a)
def point_theta(a,b):
    h=q+(Q('114.671')+Q('1.78')*eu(-a/6))*eu(-a/2)
    if b<=58:
        h=min(h,c*a*a*eu(-a/2))
    return h
def reanchor(a,b):
    return point_theta(a,b)+conv(a)+Q('2.36')*eu(-a/2)/a
def reanchor_up(a,b):
    return point_theta(a,b)+conv(a)-Q('1.9998')*el(-b/2)/b*(1-eu((s0-a)/2))
def err(a,b):
    v=[]
    if b<=A0:v.append(short(a))
    if b<=AC and a>=26:v.append(chlow(a))
    if b<=58:v.append(c*a**3*eu(-a/2))
    if a>=40:
        v.append(reanchor(a,b))
        v.extend([h0(a)+m0(a),smooth(a),h0(a)+mstar(a)])
        if b<=58:v.append(anchored(a))
    if a>=185:v.append(hi(a,theta_new(Q((4*a)//1,4))))
    return min(v)

# Coefficient after subtracting sum_{k=4}^{j-1}C[k]L^(4-k), 
# divided by L^(4-j). R remainder from H,V and normalized pi.
def rem(a,b,j):
    return (sum(Q(C[k])*b**(j-k) for k in range(j,21)) -
            sum(Q(S[k])*a**(j-k) for k in range(21,41)))
def costs(a,b,j):
    e=V(a)+(0 if b<=A0 else err(a,b))
    if a>=40 and b>A0:
        e=min(e,V(a)+reanchor_up(a,b))
    if a>=27 and b<=AC:
        e+=-Q('.2089')*el(-b/2)+Q('1.84')*(a/18)*eu(9-a)
        # Lower bound the magnitude of the negative integral using v<=u.
        e-=Q('.4178')*el(-b/2)/b*(1-eu((18-a)/2))
    assert H(b)+e>0
    squared=(a**j*e*(2*H(b)+e) if e<0 else b**j*e*(2*H(a)+e))
    return b**j*a/(a-1)*err(a-1,b-1)+squared
def tail(a,j,margin,full=False):
    # For j<=20 all the j-scaled analytic errors decrease on [a,infty).
    p=theta_new(a-1)
    e=V(a)+hi(a,p)
    cost=a**j*(a/(a-1)*hi(a-1,p)+e*(2*H(a)+e))
    neg=sum(Q(S[k])*a**(j-k) for k in range(21,41))
    pos=sum(Q(C[k])*a**(j-k) for k in range(j+1,21)) if full else 0
    return C[j]+pos-margin-cost-neg

# (real start, finite end, j, margin), all decimal rationals.
# L^6 R/x^2 > sum_{4<=k<j} C[k]/L^(k-4)+margin/L^(j-4).
ROWS=[
 ('27.8',191,4,'.04'), ('28.3',191,4,'.30'),
 ('29.2',191,4,'.70'), ('30.75',191,4,1),
 ('34.3','43.7',4,'1.40'),
 ('47.7',191,6,8), ('47.8',187,6,10), (48,184,6,25), (50,158,6,100),
 (53,122,7,0), (56,106,7,1000),
]
RUNGS=[
 (191,6,10),(222,7,0),(255,8,0),(289,9,0),(324,10,0),
 (359,11,0),(395,12,0),(430,13,0),(466,14,0),(503,15,0),
 (539,16,0),(575,17,0),(611,18,0),(648,19,0),(687,20,0),(1000,20,Q(C[20],2)),
]
EXTRA=[
 ('27.75',191,4,'.04'), ('28.24',191,4,'.30'), ('29.19',191,4,'.70'),
 ('30.59',191,4,1), ('27.8',191,4,'.06'), ('28.3',191,4,'.33'),
 ('29.2',191,4,'.715'), ('30.75',191,4,'1.03'),
 ('34.3','43.7',4,'1.405'),
 ('47.64',191,6,8),('47.645',191,6,'8.30'),('47.647',191,6,'8.34'),
 ('47.68',187,6,10),('47.97',184,6,25),('56',105,7,1050),
 ('189.36',191,6,10), ('189.9',191,6,14),
]
EXTRA_TAILS=[
 (221,7,0),(254,8,0),(288,9,0),(323,10,0),(394,12,0),
 (502,15,0),(538,16,0),(647,19,0),(191,6,16),
]
def adapt(st,en,j,z):
    a,b,Z=Q(st),Q(en),Q(z)
    endpts=sorted({a,b}|{x for x in [AC,AC+1,A0,A0+1,Q(58),Q(59),Q(185),Q(186)] if a<x<b})
    stk=list(reversed(list(zip(endpts,endpts[1:]))))
    worst=Q(10**30)
    count=0
    while stk:
        u,t=stk.pop()
        k=rem(u,t,j)-costs(u,t,j)-Z
        if k>0:
            worst=min(worst,k)
            count+=1
        elif t-u<=Q(1,4096):
            return k,count,u,t
        else:
            m=(u+t)/2
            stk.extend([(m,t),(u,m)])
    return worst,count,a,b

def check_rows():
    li_anchor()
    assert 10**11<el(Q('27.8'))<eu(Q('27.8'))<Q('1.15e16')
    assert eu(A0)<10**19 and eu(AC)<10**13 and el(Q(18))>10**4
    assert Q('.751')+Q('1.000000147')+Q('1.78')*eu(Q(-3))<Q('1.84')
    assert Q('1.95')+Q('3.9')/18+Q('19.5')/18**2+36*eu(Q(-9))<Q('2.24')
    assert Q('.2089')-Q('1.84')*Q(26,18)*eu(Q(-4))>Q('.16')
    assert Q('.2089')-Q('1.84')*Q(27,18)*eu(Q(-9,2))>Q('.17')
    assert eu(Q(58))<Q('2.169e25')
    s=s0
    assert Q(1,2)-2/s>Q('.433')
    assert Q(7,8)-2/s>Q('.8')
    assert Q('.0463')*(1+1/Q('.433'))<Q('.155')
    assert Q('3.2e-12')*(1+1/Q('.8'))==Q('7.2e-12')
    assert Q('1.000000147')+Q('1.78')*eu(-s/6)<Q('2.36')*Q('.433')
    assert short(s)/el(-s/2)-Q('.2089')<Q('2.2')
    assert (Q('2.2')/s
        +(Q('.0463')+Q('3.2e-12')*eu(3*s/8)+4*eu(-s/2))/s**2
        +2*eu(-s/2)/s)<Q('.074')
    assert c*40**2<64 and 4+12*fac(21)*eu(Q(40))/40**22<1000
    assert theta_coeff(Q(190))<P
    L=Q(40)
    high=Q('3.2e-12')
    low=Q('.083')
    assert (3+low)*Q(20,9)+low<7
    assert high*(1+Q(40,33))<Q('8e-12')
    assert (low+high*eu(Q(15))+2*eu(-L/2))/L**2+(2/L+2/L**2)*eu(-L/2)<Q('.01')
    assert h0(Q(190))<q+Q('1e-30')
    assert err(Q(26),Q(26))<1 and h0(Q(40))+m0(Q(40))<1
    for st,en,j,z in ROWS:
        a,b,Z=Q(st),Q(en),Q(z)
        endpts=sorted({a,b}|{x for x in [AC,AC+1,A0,A0+1,Q(58),Q(59),Q(185),Q(186),Q(190)] if a<x<b})
        worst=Q(10**30); arg=a
        for u,v in zip(endpts,endpts[1:]):
            while u<v:
                d=Q(1,400) if 189<=u<191 else Q(1,50) if u<60 or u>=180 else Q(1,10)
                t=min(u+d,v)
                k=rem(u,t,j)-costs(u,t,j)-Z
                if k<worst: worst,arg=k,u
                u=t
        print('whole cells',st,en,j,z,'slack',float(worst),'near',float(arg),flush=True)
        assert worst>0
    assert tail(Q(191),5,Q(0))>0
    for a,j,z in RUNGS:
        k=tail(Q(a),j,Q(z))
        print('analytic tail',a,j,z,'slack',float(k),flush=True)
        assert k>0

if __name__=='__main__':
    import sys
    if sys.argv[1:]!=['extra']:
        check_rows()
    if sys.argv[1:]!=['locked']:
        for st,en,j,z in EXTRA:
            k,n,a,b=adapt(st,en,j,z)
            print('adaptive cells',st,en,j,z,'slack',float(k),'cells',n,'bounds',float(a),float(b),flush=True)
            assert k>0
        for a,j,z in EXTRA_TAILS:
            k=tail(Q(a),j,z,True)
            print('analytic full tail',a,j,z,'slack',float(k),flush=True)
            assert k>0
