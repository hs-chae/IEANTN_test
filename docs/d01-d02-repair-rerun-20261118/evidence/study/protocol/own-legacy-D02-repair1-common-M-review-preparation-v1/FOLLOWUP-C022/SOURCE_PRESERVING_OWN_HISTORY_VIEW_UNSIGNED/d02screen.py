"""Directed rational certificates for the new density / cutoff screen."""
from d02rigor import *
from math import factorial as fac, comb
from functools import lru_cache
a=F(5,32); b=1-a
H=3000175332800
h=log(H)
lh=log(h); l3=log(3)
A0=PI/(3*10**12)
s0=F('0.72')
t0=F(155)
# Upward rounding, by at least one last-digit unit, of minima-candidates
# from each applicable block in the first panel of FKS Table 8.
old=[(70,'6.173','4.500'),(75,'7.798','4.101'),(80,'8.162','3.693'),
     (81,'8.538','3.613'),(82,'8.928','3.533'),(83,'9.331','3.453'),
     (84,'9.747','3.373'),(85,'10.177','3.293'),(86,'10.621','3.213'),
     (87,'11.077','3.133')]
def minI(*v):
    return I(min(I(x).lo for x in v),min(I(x).hi for x in v))
def maxI(*v):
    return I(max(I(x).lo for x in v),max(I(x).hi for x in v))
def U(x):
    return I(I(x).hi,I(x).hi)
def D(x):
    return I(I(x).lo,I(x).lo)
def e(x): return exp(x)

@lru_cache(None)
def masses(s,m=1,dusart_only=False):
    q=5-2*s; p=8*(1-s)/3
    z=(m-p)*h
    A=sum(I(comb(3,j)*fac(j))/z**j for j in range(4))
    B=sum(I(comb(3,j)*fac(j+1))/z**(j+1) for j in range(4))
    f=2*m*e(-z+q*lh)/(m-p)*A*e((q-3)*log(1+B/A))
    zm=m*h
    g=2*e(-zm)*(h*h+2*h/m+I(2)/m**2)
    values=[(0,I('4.9')*e(p*l3)*f+I('51.5')*g)]
    if not dusart_only:
        for tab in (old,):
            k,c,d=next((j,c,d) for j,c,d in reversed(tab) if F(j,100)<=s)
            values.append((k,I(c)*f+I(d)*g))
    return tuple(values)

@lru_cache(None)
def mass(s,m=1,dusart_only=False):
    return minI(*(v for k,v in masses(s,m,dusart_only)))

@lru_cache(None)
def table(B=b,m=1,dusart_only=False,step=F(1,4000)):
    s=s0; rows=[]
    w=None
    while s<B:
        r=min(s+step,B)
        v=U(mass(s,m,dusart_only))
        if w is not None: v=minI(w,v)
        rows.append((s,r,v))
        w=v; s=r
    return tuple((r,v-(rows[j+1][2] if j+1<len(rows) else I(0)))
                 for j,(_,r,v) in enumerate(rows))

@lru_cache(None)
def high(L,B=b,m=1,dusart_only=False):
    x=I(L)
    # Horner on the regular part; explicit factor for the last (short) strip.
    rows=table(B,m,dusart_only)
    z=I(0); step=rows[0][0]-s0
    E=e(-step*x)
    for r,v in rows[:-1]:
        z=z*E+v
    d=(B-rows[-2][0])*x
    v=rows[-1][1]
    w=U(mass(B,m,True))
    assert U(mass(rows[-2][0],m,True)).hi==v.hi and w<v
    return z*e(-d)+w+(v-w)*(1-e(-d))/d

@lru_cache(None)
def chords(m=1):
    rows=table(b,m,False)
    weights=[sum(v for _,v in rows[j:]) for j in range(len(rows))]
    uniform=[]
    for i,(r,v) in enumerate(rows):
        l=rows[i-1][0] if i else s0
        R,L=dict(masses(r,m)),dict(masses(l,m))
        wr=weights[i+1] if i+1<len(rows) else U(mass(b,m,True))
        for k in L.keys() & R.keys():
            if U(L[k]).hi==weights[i].hi and U(R[k]).hi==wr.hi:
                uniform.append((r,r-l,weights[i]-wr))
                break
    assert uniform[-1][0]==b
    return tuple(uniform)

@lru_cache(None)
def better_high(L,m=1):
    rows=table(b,m,False)
    # Group all the uniform bins of common width. Only the last bin
    # can have smaller width. Add the allowable atom at the cap.
    x=I(L); t=rows[0][0]-s0; E=e(-t*x)
    U0={r:v for r,d,v in chords(m)}
    uni=atom=I(0)
    for r,v in rows[:-1]:
        wu=U0.get(r,I(0))
        uni=uni*E+wu; atom=atom*E+v-wu
    tail=I(b-rows[-2][0])*x
    return ((atom+uni*(1-E)/(t*x))*e(-tail)+U(mass(b,m,True))
            +U0[b]*(1-e(-tail))/tail)

@lru_cache(None)
def sharp(L,c=F(27,100)):
    x=I(L); y=c*x+log(I('2.45')); v=log(2*PI)
    return (better_high(L)+(((y-v)**2-(h-v)**2)/12+I('.1'))*e(-(b-s0)*x)
             +(y*y/6+3)*e(-(b-F(1,2))*x)+I('2.091')*x*e(-(c-a)*x))

@lru_cache(None)
def screen(L,B=b,dusart_only=False,c=F(2,5)):
    """Strong power coefficient, two optional choices of c evaluated separately."""
    if not dusart_only and B==b: return minI(classic(L,B,dusart_only,c),sharp(L))
    return classic(L,B,dusart_only,c)

def classic(L,B,dusart_only,c):
    x=I(L); y=c*x+1
    return (high(L,B,1,dusart_only)
             + ((y*y-h*h)/12+I('.1'))*e(-(B-s0)*x)
             + (y*y/6+3)*e(-(B-F(1,2))*x)
             + I('2.091')*x*e(-(c-(1-B))*x))

@lru_cache(None)
def scr2(L,B=b,dusart_only=False):
    return high(L,B,2,dusart_only)+I('7e-12')*e(-(B-s0)*I(L))

def triangle(L):
    x=I(L); c=F(19,100); y=c*x+1
    return (((y*y-h*h)/12+I('.1'))
             +(y*y/6+3)*e(-(b-F(1,2))*x)
             +I('2.091')*x*e(-(c-a)*x))
def prelim():
    pi_check()
    for U0 in (I(100),I(H)):
        l=log(U0)
        r=I('.137')*l+I('.443')*log(l)+I('1.588')
        c=1/(2*PI)+(I('.137')*l+I('.443'))/(U0*l*log(U0/(2*PI)))
        assert c<I(F(1,6)) and 2*r/U0<I('.1')
    assert e(1)>I('2.45') and e(F(7,20)*t0)>max(51,t0)
    assert e(3*t0/20)>6 and e(t0/2)>2
    assert I(F(7,20)*t0+1)**2>2*h*h
    assert 4/t0 < b-s0 and 2/t0<b-F(1,2)
    assert I('18.42')>4
    assert (F(1,2)-a)>0
    assert I(F(19,100)*t0+1)>h and e(F(19,100)*t0)>t0
    assert (triangle(t0)+h*h/12)/I(t0)**2<I('.0034')
    c=F(27,100); Y=c*t0+log(I('2.45')); v=log(2*PI)
    assert Y>h
    # Since the additive shift in Y-v is negative, test 4/L using
    # the polynomial inequality 2[(Y-v)^2-(h-v)^2] >= cL(Y-v).
    o=log(I('2.45'))-v
    assert 2*((Y-v)**2-(h-v)**2)>c*t0*(Y-v)
    assert 2*c*t0+3*o>0 and c-a>1/t0
    assert e(c*t0)>t0 and e(t0/2)>2 and e((F(1,2)-c)*t0)>6
    assert mass(b)<I('.116297') and mass(b,2)<I('2.506e-14')
    assert mass(F(7,8))>I('.00666')
    assert (h*h/12-I('.1'))>0
    # B0 already gives the exact D01 bound via QRH and the FKS cutoff.
    L=I(200)
    assert e(L/4)>L and e(L/2)>2 and e(L/4)>6
    assert (((L/4+1)**2/6+3)/L**2+I('2.091')*e(-L/8)/L)<F(1,64)

def main():
    prelim()
    for BB in (b,F(7,8)):
        for L in (155,160,165,166,167,168,169,170,175,180,190,200,250,300,400,600,1000):
            z=[screen(F(L),BB,c=c) for c in (F(7,20),F(2,5),F(9,20))]
            print(BB,L,*z,'bulk', minI(*z)*e(-(1-BB)*I(L)))
        print("limit, smoothed limit",mass(BB),mass(BB,2))
    print("Dusart-only",screen(168,dusart_only=True),screen(200,dusart_only=True))
if __name__=='__main__': main()
