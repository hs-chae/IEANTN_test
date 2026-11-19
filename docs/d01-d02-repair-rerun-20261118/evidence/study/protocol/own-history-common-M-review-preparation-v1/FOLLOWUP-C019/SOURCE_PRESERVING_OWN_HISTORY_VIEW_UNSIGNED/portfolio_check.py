"""Current D01 arithmetic certificates. Python 3.10, exact interval arithmetic."""
from refine import W2, I, F, PI, H, h, a0, e, log, upper, maincmp, Acoef, pi_check
from functools import lru_cache
from math import factorial as fac
import sys
DUSART_ONLY="--dusart-only" in sys.argv
QRH_FREE_PREFIX="--qrh-free-prefix" in sys.argv

b=F(7,8)
s0=F(7,10)
cuts=[s0+F(j,10000) for j in range(1751)]
def minimum(x,y):
    return I(min(x.lo,y.lo),min(x.hi,y.hi))
def weights():
    w=[]
    for s in cuts[:-1]:
        z=h; lam=(8*I(s)-5)/3; q=5-2*I(s); k=lam*z
        f=1+q/k+(6+6*(q-3))/k**2+(6+18*(q-3))/k**3+24*(q-3)/k**4
        tmp=2*e(-k+q*log(z))/lam*f
        tmp2=2*e(-z)*(z*z+2*z+2)
        # Dusart Thm 2.3, log(1+w)<=w, compared to FKS at each s.
        wD=I('4.9')*e((1-lam)*log(3))*tmp+I('51.5')*tmp2
        if DUSART_ONLY:
            wj=wD
        else:
            wF=(I('6.173')*tmp+I('4.500')*tmp2 if s<F(3,4) else W2(s,h))
            wj=minimum(wF,wD)
        w.append(minimum(w[-1],wj) if w else wj)
    w.append(I(0))
    return [I(max(0,(x-y).lo),max(0,(x-y).hi)) for x,y in zip(w,w[1:])]
Z=None
@lru_cache(None)
def spectral(L):
    """Upper bound for scaled psi error, notably NO extra cutoff tail."""
    global Z
    if Z is None: Z=weights()
    x=I(L)
    u=e(-x/10000)
    res=I(0)
    for v in Z:
        res=res*u+v
    y=I('.45')*x+1
    return res+(y*y/12+1)*e(-F(7,40)*x)+(y*y/6+3)*e(-F(3,8)*x)+I('2.091')*x*e(-F(13,40)*x)
def bpi(L):
    x=I(L)
    return e(-x/2)*(I('1.95')+I('3.9')/x+I('19.5')/x**2)+4*x*e(-x)
def fpi(L):
    x=I(L); return (x*x+2*x)*e(-x/2)/(8*PI)+1354*x*e(-x)
def cres(L):
    x=I(L);return a0/(I('.9')*x)+117*e(-x/2)/(I('.4')*x)+3*x*e(10-x)
def cpi(L):
    x=I(L);return a0+117*e(-x/2)+cres(L)
def hsm(L):
    x=I(L); a=I(20)
    def j(t): return I('.04620')*e(-t/2)+2*e(-t)+I('7e-12')*e(-t/8)
    at=3*a*e(10-a)+j(a)/a
    return at*(x/a)*e(a-x)+j(x)/x+I('3.04620')*e(-x/2)/(I('.4')*x)+I('7e-12')*e(-x/8)/(I('.775')*x)+2*x*e(-x)/a
def csm(L):
    x=I(L)
    return a0+117*e(-x/2)+minimum(cres(L),hsm(L))
@lru_cache(None)
def spi(L):
    x=I(L)
    a=F(180)
    boundary=spectral(L)*e(-x/8)+3*e(-x/2)
    rr=(I('.01361')*e(-x/8)/(x*(I(b)-2/a))
        +3*e(-x/2)/(x*(I('.5')-2/a))
        +I('7e-15')*x/a*e(a-x))
    return boundary+minimum(minimum(rr,cres(L)),hsm(L))
def direct_pi(L):
    x=I(L)
    j=(x*x+I(8)*x/7)*e(-x/8)/64
    j+=3*e(-x/2)*(1+1/(x*(I('.5')-I(1)/100)))
    return j+I('7e-15')*x/200*e(200-x)
def bound(L,top):
    """L is left endpoint; top is right endpoint; result bounds whole cell."""
    z=cpi(L)
    if top<=F('43.7'): z=minimum(z,bpi(L))
    if top<=58: z=minimum(z,fpi(L))
    if L>=58 and not QRH_FREE_PREFIX: z=minimum(z,csm(L))
    if L>=180 and not QRH_FREE_PREFIX: z=minimum(z,spi(L))
    return z
@lru_cache(None)
def loss(l,r,one=False,kind=None,norm=4):
    x=I(l)
    if kind is None:
        d=bound(l,r);a=bound(l-1,r-1)
    else: d=kind(l);a=kind(l-1)
    return I(r)**norm*(x/(x-1)*a+((I(3)*x*e(-x))*(2*upper(x)+I(3)*x*e(-x)) if one else d*(2*upper(x)+d)))
@lru_cache(None)
def eps(l):
    x=I(l)
    if l<180: return maincmp(l)
    pp=sum(I(fac(k))/x**k for k in range(18))
    ds=4*x*e(-x)+2*I(fac(18))/x**18+x*e(-x/2)
    tail=sum(I(fac(j)*fac(k))/x**(j+k-4) for j in range(18) for k in range(18) if j+k>=18)
    return minimum(maincmp(l),tail+x**4*((2*pp+ds)*ds+36*x/(x-1)*e(2-x)))
C=[Acoef(i) for i in range(4,18)]
def checkcell(l,r,m,one=False,offset=0,skip=None):
    x=I(r)
    p=sum(I(k)/x**(j-offset) for j,k in enumerate(C) if j>=offset)
    return p-loss(l,r,one,skip,4+offset)-eps(l)*I(r)**offset>I(m)
def cover(a,b,step,margin,one=False,offset=0,kind=None):
    l=F(a); b=F(b)
    while l<b:
        r=min(b,l+F(step))
        assert checkcell(l,r,margin,one,offset,kind),(l,r,margin,offset)
        l=r
def first_checks():
    pi_check()
    assert [Acoef(i) for i in range(4)]==[0,0,0,0] and all(k>0 for k in C)
    assert C[:7]==[1,14,145,1412,13985,145450,1610021]
    assert e(F('43.7'))<10**19
    assert e(58)<I('2.169e25') and log(2)>I('2')/3
    assert I(18)/(1-I(17)/27)<49  # smaller exact moment-tail bound checked separately below
    assert sum(1/(1-I(j)/27) for j in range(18))<36
    assert e(1)>I('2.45') and e(F('76.5'))>200 and e(F('8.5'))>6
    assert cres(180)<I('7e-15') and cres(200)<I('7e-15')
    assert spectral(F(180))<I('.01361')
    for L,k in [(190,'.012904' if DUSART_ONLY else '.012902'),
                (200,'.0123291' if DUSART_ONLY else '.012329'),
                (250,'.0105496'),(300,'.0096255'),
                (400,'.0086767'),(1000,'.0073709')]:
        assert spectral(F(L))<I(k)
        print("psi coefficient at",L,spectral(F(L)))
    assert Z[-1]<I('.00673')
    assert ((I(51)**2/6+3)/200**2+I('2.091')*e(-25)/200)<I(1)/64
    assert I('113.67')+I('1.000000147')+I('1.78')*e(-log(2)/6)<117
    assert e(F('29.9'))<10**13
    assert e(F(174)/3)>10**25
def ram_checks():
    for a,c in [('28.15','.01'),('28.35','.1'),('28.65','.25'),
                 ('29.15','.5'),('30','.8'),('30.8','1')]:
        cover(a,43,F(1,100),c,True)
    for a,b0,st in [(43,'43.7',F(1,16)),('43.7',44,F(1,32)),(44,58,F(1,8)),
                    (58,180,F(1,4)),(180,191,F(1,20))]:
        if not QRH_FREE_PREFIX or F(b0)<=180: cover(a,b0,st,'1')
    # Strong intermediate profiles on nested or bounded intervals.
    for a,b0,st,m,one in [(35,43,F(1,32),20,True),(43,'43.7',F(1,32),20,False),
        (49,58,F(1,16),30,False),(58,180,F(1,4),30,False),
        (50,58,F(1,32),90,False),(58,164,F(1,4),90,False),
        (49,58,F(1,16),22,False),(58,180,F(1,4),22,False),
        (180,185,F(1,20),22,False),(185,187,F(1,200),22,False),
        (187,188,F(1,50),22,False)]:
        if not QRH_FREE_PREFIX or F(b0)<=180: cover(a,b0,st,m,one,2)
    if QRH_FREE_PREFIX:
        print('QRH-free prefix claims through L=180 passed')
        return
    assert loss(F(188),F(188),kind=spi,norm=6)+eps(188)*188**2<C[2]-22
    for L,j in [(219,3),(253,4),(286,5),(320,6),(355,7),(391,8),
                (426,9),(467,10),(508,11),(552,12),(595,13)]:
        v=loss(F(L),F(L),kind=spi,norm=4+j)+eps(L)*L**j
        print("higher profile (L,next index) and loss/next:",L,j,v/C[j],flush=True)
        assert v<C[j],(L,j)
    # Density-table-free quantitative ray.
    for a,b0,st in [(50,58,F(1,8)),(58,275,F(1,2))]:
        cover(a,b0,st,3,False,1,kind=cpi if a>=58 else None)
    assert loss(F(275),F(275),kind=direct_pi,norm=5)+eps(275)*275<C[1]-3
    # Shrunk argument (A3), with the now-corrected initial integral.
    d=I('1.001'); A=I(58); U=I(188)
    flat=a0*(1+1/(I('.9')*(A-d)))
    tails=cpi(A-d)-flat
    assert 2*A/(A-d)*(U**5*flat+A**5*tails)<I('.58')
    assert 2*U**6/(U-d)*spi(F('186.999'))<I('.58')
    assert (12+d)/(1-d/58)<I('13.23')
    assert (1+I(12)/58)/I(58)**4<1-e(I('-.001'))
    print("Ramanujan cells and monotone tails passed")

if __name__=='__main__':
    if not QRH_FREE_PREFIX: first_checks()
    ram_checks()
