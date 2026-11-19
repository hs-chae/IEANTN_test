from analytic import *
from math import isqrt, inf
CU=I('1.000000147')
DCT=I('113.67')
FALL=I(b)
def pospart(a):
    a=cv(a);return I.raw(max(0,a.lo),max(0,a.hi))
def mn(*a):
    return I.raw(min(v.lo for v in a),min(v.hi for v in a))
def mx(*a):
    return -mn(*(-v for v in a))
def parts(L, *, normalized=False, finite_bias=None, spectral=None, gap=F(1,8)):
    # Explicit enclosures of errors and positive power tails; L>=13
    r=ex(-L/2); s=ex(-2*L/3); t=ex(-L)
    a=L/2
    w=FALL+DCT*r
    wcap=w
    if normalized and 5*L.hi<=138*S: wcap=mn(w,I('.8')*r)
    kfin=a*a/(8*PI)*ex(-a/2)
    kc=thetaCH(a)
    if a.hi<=58*S: 
        # K must bound |theta(e^v)/e^v-1| for ALL v>=a.
        K=mn(kc,mx(kfin,thetaCH(I(58))))
    else: K=kc
    K=mn(K,I('1.2323')/a)
    for eta,k,X in [('.001',1,908994923),('.2',2,3594641),('.05',2,122568683),('.01',2,7713133853),('.5',3,767135587)]:
        if a.lo>=I(X).log().hi:K=mn(K,I(eta)/a**k)
    bl=pospart((2*(1-K)-CU)*r-I('1.78')*s)
    bu=(2*CU-1+K)*r+I('2.67')*s
    if finite_bias is not None and L.hi<=22*S:
        bi,ai=finite_bias(L)
        bl=mx(bl,I.raw(bi.lo,bi.lo)); bu=mn(bu,I.raw(bi.hi,bi.hi))
    al=pospart(bl/L-((2*CU-1+K)*2*r+I('4.005')*s)/L**2)
    au=bu/L
    if finite_bias is not None and L.hi<=22*S:
        al=mx(al,I.raw(ai.lo,ai.lo)); au=mn(au,I.raw(ai.hi,ai.hi))
    # integer telescoping tail for p>x: 1/(2 floor x) <= 1/(2(x-1)).
    c=t/(2*(1-t))
    p=FALL+DCT*r
    pm=p
    if L.hi<=58*S:
        p=mn(p,L*L/(8*PI)*r)
        if L.lo>=30*S:p=mn(p,optimized_ch(L,True))
        if L.lo>=34*S:p=mn(p,optimized_ch(L),optimized_ch(L,ratio=F(13,20)))
        if L.lo>=35*S:p=mn(p,optimized_ch(L,ratio=F(2,5)))
        pm=mn(pm,p)
    if 10*L.hi<=299*S: p=mn(p,I('.791')*r);pm=mn(pm,I('.751')*r)
    if L.lo>=100*S:
        e=mn(spec(L),refined(L))
        p=mn(p,e);pm=mn(pm,e)
    if spectral is not None and L.lo>=86*S:
        e=spectral(L); p=mn(p,e); pm=mn(pm,e)
    j=I('.12')*r+I('.000000000008')*ex(-gap*L)
    # The real nonzero constant term -log(2pi) is accounted for by the
    # absolute 1.84 e^-L bound on its integrated contribution.
    k=j+I('1.84')*t
    # Same integral bound on the constant/trivial contribution divided by L.
    d=mn(wcap,p+k)
    dm=mn(wcap,pm+k)
    jw=2*DCT*r/L**2+FALL/L
    if normalized and L.hi<=27*S:
        v=I(27)
        jw=mn(jw,I('1.6')*r/L**2+2*DCT*ex(-v/2)/v**2+FALL/v)
    zp=mn(wcap/L+jw,(p+(1+1/L)*j+I('1.84')*t)/L)
    zm=mn(wcap/L+jw,(pm+(1+1/L)*j+I('1.84')*t)/L)
    return (-zm+pospart(al-c),zp+au),(-zm+al,zp+au),(-dm+bl,d+bu)
def rad0(l,u):return mx(-l,u)
def bounds(L, **kw):
    (l,u),s,w=parts(L,**kw)
    return mx(1-ex(-u),ex(-l)-1),mx(ex(u)-1,1-ex(l)),rad0(*s),rad0(*w)
