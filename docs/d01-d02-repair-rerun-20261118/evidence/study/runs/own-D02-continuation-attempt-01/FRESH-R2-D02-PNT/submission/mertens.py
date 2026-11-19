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
def parts(L, *, normalized=False, finite_bias=None, spectral=None):
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
        if spectral is not None: e=mn(e,spectral(L))
        p=mn(p,e);pm=mn(pm,e)
    j=I('.12')*r+I('.000000000008')*ex(-L/8)
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
def tail(L, C):
    r=ex(-3*L/8);s=ex(-(F(2,3)-F(1,8))*L)
    e=I('.04')*L**2*ex(-F(3,40)*L)+13*L*r+sum(c*ex(-(g-F(1,8))*L) for c,g,h in LS)
    e+=I('.12')*r+I('.000000000008')+I('1.84')*ex(-7*L/8)
    bu=I('1.002')*r+I('2.67')*s
    # For L>=200, Dusart k=3 at e^(L/2) gives K<.001.
    assert low(I('.001'),I('.5')/(L/2)**3)
    # bound x^(1/8) * absolute log-errors * L, and sum-log error.
    a=e+bu+(I('.12')*r+I('.000000000008'))/L
    assert low(I(C),a/(1-a*ex(-L/8)/L))
    print('power tail at',L,'constant',C,'unrounded',a)
def test_poly(start,end, cs, **kw):
    ci=[(k,F(c)) if k else None for k,c in cs]
    def try_interval(l,h):
        L=bracket(l,h)
        if h-l>1: raise ValueError()
        z=bounds(L,**kw)
        if all(v is None or low(v[1],u*L**v[0]) for u,v in zip(z,ci)):return
        if h-l<F(1,4096):raise ValueError((l,h,z,ci))
        m=(l+h)/2
        try_interval(l,m);try_interval(m,h)
    a=start
    while a<end:
        b=min(end,a+1)
        for t in (22,27,F('27.6'),F('29.9'),58,100):
            if a<t<b:b=t;break
        try_interval(F(a),F(b));a=b
    for j,v in enumerate(ci):
        if not v:continue
        k,c=v
        e=I('.021')*ex(-I(end)/8)*I(end)**(k-(j!=3))
        assert end>=8*(k-(j!=3)) and low(I(c),e)
    print('poly:',start,cs)
def test_early_power(C, **kw):
    # At 200 the independent whole-ray bound takes over.
    def run(a,b):
        L=bracket(a,b)
        w=bounds(L,**kw)
        checks=[low(I(C)*ex(-L/8),v*(L if j<3 else 1)) for j,v in enumerate(w)]
        if all(checks):return
        assert b-a>F(1,4096),(a,b,w)
        m=(a+b)/2
        run(a,m); run(m,b)
    for a in range(13,200):
        for lo,hi in [(F(a),F(a+1))] if a not in (27,29) else (
            [(F(a),F('27.6')),(F('27.6'),F(a+1))] if a==27 else [(F(a),F('29.9')),(F('29.9'),F(a+1))]):
            run(lo,hi)
    assert F(C)>F('.0196')
    print('early power from L=13, coefficient',C)
def sieve(N):
    b=bytearray(N+1);b[:2]=b'\1\1'
    for p in range(2,isqrt(N)+1):
        if not b[p]:b[p*p:N+1:p]=b'\1'*((N-p*p)//p+1)
    return [p for p in range(2,N+1) if not b[p]]
def scan(N=2278383, NC=10**7):
    qp=sieve(NC)
    pp=[p for p in qp if p<=N]
    Z=W=T=B=I(0)
    targets=[(j,3,F(c),N-(j<2)) for j in range(3)
             for c in ['.2','.202','.21','.225','.25','.275','.3']]
    targets += [(3,2,F(c),912560) for c in ['.3','.301','.31','.33','.36','.4']]
    bad={v:2 for v in targets}
    # All constants enclosing intervals. z_p = -log(1-1/p).
    for p in qp:
        lp=I(p).log()
        z=-I.raw(*lnq(p-1,p))
        T+=z-I(1)/p
        B+=lp/(p*(p-1))
    G=gamma()
    L=I(NC).log(); K=I('.0007')
    assert low(K, I('1.791000147')*ex(-L/2)+I('1.78')*ex(-2*L/3))
    z=I('29.9')
    assert low(K,mx(z*z/(8*PI)*ex(-z/2),thetaCH(I(58))))
    vs=-I.raw(*lnq(NC-1,NC))
    vspan=K*(2*I(1)/(NC-1)+vs)
    B3=G+B+I.raw((vs-vspan).lo,(vs+vspan).hi)
    main=(1-1/L+2/L**2-6/L**3+24/L**4)/(2*NC*L)
    lower=main-120/(2*NC*L**6)
    vspan=K*3/(2*NC*L)
    rem=I(1)/(3*(NC-1)**2)
    M=G-T-I.raw((lower-vspan).lo,(main+vspan+rem).hi)
    print('constants',M,B3,'sieve count',len(pp))
    clips=[(j,F(start),end,F(c)) for j,start,end,c in [
        (0,'2278381.72',N-1,'.2'),(1,'2278381.72',N-1,'.2'),
        (2,'2278382.13',N,'.2'),(3,'912559.998',912560,'.3')]]
    clipbad=set()
    witnesses={ (1,F('2278381.70'),F('.2')), (2,F('2278382.1'),F('.2')),
                (3,F('912559.996'),F('.3')) }
    checked=set()
    Y=I(0)
    for p,q in zip(pp,pp[1:]+[N]):
        lp=I(p).log();lq=I(q).log()
        Z-=I.raw(*lnq(p-1,p)); W+=I(1)/p;Y+=lp/p
        if q<=2000:continue
        ll=lp.log();lq2=lq.log()
        def cell(lp,lq):
            ll=lp.log();lq2=lq.log()
            ds1=W-ll-M; ds2=W-lq2-M
            dt1=Y+B3-lp; dt2=Y+B3-lq
            zl=Z-G-ll; zr=Z-G-lq2
            ql=ex(zl);qr=ex(zr)
            pl=1/ql;pr=1/qr
            assert low(pl,F(3,4)) and low(F(3,2),ql)
            assert low(I(1)/3,ds1) and low(lp/2,dt1)
            return [mx((1-pl)*lp**3,(pr-1)*lq**3),
                    mx((ql-1)*lp**3,(1-qr)*lq**3),
                    mx(ds1*lp**3,-ds2*lq**3),mx(dt1*lp**2,-dt2*lq**2)]
        f=cell(lp,lq)
        for j,end in enumerate([N-1,N-1,N,912560]):
            if p<=end<=q:
                xe=I(end).log()
                print('original onset adjoining cell audit',j,p,q,end,cell(xe,xe)[j])
        for j,start,end,c in clips:
            lo=max(p,start);hi=min(q,end)
            if lo<hi:
                w=cell(I(lo).log(),I(hi).log())[j]
                print('clipped test',j,lo,hi,w)
                if not low(c,w):clipbad.add((j,start,end,c))
        for j,x,c in witnesses:
            if p<=x<q:
                lx=I(x).log();w=cell(lx,lx)[j]
                assert low(w,c)
                checked.add((j,x,c))
                print('verified local obstruction at fixed coefficient',j,x,w)
        for v in targets:
            j,k,c,end=v
            if p<end and not low(I(c),f[j]):
                bad[v]=min(q,end)
    assert checked==witnesses
    assert not clipbad
    for v in targets:print('finite',v,'start',max(2000,bad[v]))
    for j,start,end,c in clips:
        if (j,start,end,c) not in clipbad: print('certified finite join',j,start,end,c)

if __name__=='__main__':
    import sys
    if 'scan' in sys.argv:scan()
    elif 'explore' in sys.argv:
        for L in [16,17,18,19,20,22,24,27,28,30,40,58,59,70,100,150,200,250]:
            u=I(L);print(L,[a*u**(3 if j<3 else 2) for j,a in enumerate(bounds(u))])
        for L in [200,225,250,300,350,400]:
            u=I(L);print(L,refined(u)*ex(u/8))
    else:
        for l,c in [(200,'.0196'),(225,'.018'),(250,'.017'),(300,'.016'),(350,'.015'),(420,'.014'),(600,'.013'),(1000,'.0119'),(2000,'.0114'),(5000,'.011')]:
            tail(I(l),c)
        test_early_power('.0215')
        for l,p in [(16,[(3,'.185')]*3+[(0,0)]),(F('17.83'),[(3,'.09')]*3+[(2,'.09')]),
                     (22,[(4,'.5')]*3+[(3,'.5')]),(34,[(5,'4')]*3+[(4,'4')]),
                     (56,[(6,'.3')]*3+[(5,'.3')])]:
            test_poly(l,240,p)
        test_poly(16,240,[(0,0)]*3+[(2,'.175')],normalized=True)
