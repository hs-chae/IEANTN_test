"""Repair-stage, whole-cell and all-ray refinements; stdlib + local intervals."""
from certificate import *
from refine import row, rp, pc, mc, rt
from math import prod, exp as approx_exp

@lru_cache(None)
def z4(s):
    h=log(H)
    cand=[]
    for a,b,c,f in row:
        if a<=s:
            u=min(s,b); q=5-2*u; d=(8*u-5)/3
            poly=sum(prod(q-i for i in range(k))/(h*d)**k for k in range(5))
            cand.append(2*c*exp(q*log(h)-d*h)*poly/d+2*f*(h*h+2*h+2)/H)
    return I(min(j.l for j in cand),min(j.h for j in cand),True)
@lru_cache(None)
def zterms(b):
    pts=sorted({F(3,4)+F(i,4000) for i in range(501) if F(3,4)+F(i,4000)<b}
        |{b}|({b1} if b==b0 else set()))
    z=[z4(s) for s in pts[:-1]]+[I(0)]
    c=[z[j]-z[j+1] for j in range(len(pts)-1)]
    assert all(t.h>=0 for t in c)
    return ((F(1,25),2,F(1,4)),(2,0,F(1,4)),(F('12.546'),1,F(1,2)),(119,0,F(1,2)))+tuple(
        (I(max(0,t.l),t.h,True),0,1-pts[j+1]) for j,t in enumerate(c))
@lru_cache(None)
def zpi(b,v):
    a=F(61); t=zterms(b)
    return transfer(t,a,v,CH(a)+value(t,a)/a)
@lru_cache(None)
def zm(b,v):
    d=1-b
    p=value(tuple((c,k,r-d) for c,k,r in zterms(b)),v)
    return product_bound(v,d,p)
def product_bound(v,d,p,scale=0):
    w=e(-(F(1,2)-d)*v)
    mass=6*w+F(400,H)
    powers=4*w+10*e(-(F(2,3)-d)*v)
    z=p+((1+1/v)*mass+powers)/v**scale
    return z/(1-z*v**(scale-1)*e(-d*v))
def real_search(g,lo,hi): # step .01 in log x; returns certified upper endpoint
    assert g(F(hi,100)), (lo,hi)
    while hi-lo>1:
        m=(hi+lo)//2
        if g(F(m,100)):hi=m
        else:lo=m
    return F(hi,100)
def buthe(v):
    return (F('1.95')+F('3.9')/v+F('19.5')/v**2)*e(-v/2)/v+2*e(-v)
@lru_cache(None)
def early_poly():
    u=F(28);kk=F(fac(25),1-F(26,u))
    t=sum(u**k/(k*fac(k)) for k in range(1,181))
    f=(I(F('.57'),F('.59'))+log(u)+I(t,t+2*u**181/(181*fac(181))))*e(-u)
    assert I(fm(u)).lt(f) and f.lt(fm(u)+kk/u**26)
    assert u*(fm(u)+kk/u**26)<F('1.04')
    z=dict(D)
    for k in range(25):z[k+27]-=2*fac(k)*(kk-K)
    z[52]-=kk*kk-K*K
    return z

def early(l,r,margin=None,j=None,step=F(1,256)):
    end=F('43.74')
    assert l>=30 and (58*e(F(-29))).lt(F('.01'))
    dd=early_poly()
    assert (37*CH(F(37),200000000)).lt(F('.01'))
    while l<r:
        h=min([l+step,r]+[cut for cut in (F('39.3'),end,end+1,F(43),F(44),F(58),F(59)) if l<cut])
        if h<=end:
            # Even allowing a shift at most 2 in the signed result.
            u=2*e(-l)
        else:
            u=err(l,b0,False) if l!=58 else CH(l)
        v=l-1
        if h-1<=end:
            w=pick([buthe(v),err(v,b0,False)])
        else:
            w=err(v,b0,False) if v!=58 else CH(v)
        loss=h**5*(w+F('2.09')*u)
        if j is None:
            low=1+sum(dd[n]*(h if dd[n]>=0 else l)**(6-n) for n in range(7,max(dd)+1))
            if not loss.lt(low-margin):return l,h
        else:
            N=j+7
            slack_here=dd[N]+sum(c*(h if c>=0 else l)**(N-n) for n,c in dd.items() if n>N)
            if not (loss*h**(j+1)).lt(slack_here):return l,h
        l=h
    return None
def scaled(b,v,L,j,a,t):
    d=1-b
    g=(j+6)*log(L)
    anchor=CH(a)+value(t,a)/a
    # Combine the large normalization with the small common power before exp.
    return anchor*exp(g+a-v)+exp(g-d*v)/v*sum(
        c*v**k*e(-(r-d)*v)*(1+1/(v*(1-r-F(2,a)))) for c,k,r in t)

def scaled_pi(b,v,L,j):
    return scaled(b,v,L,j,F(61),zterms(b))

def suggest(b,j,sl,lo,hi,cert):
    # Non-proof endpoint suggestions only; every reported endpoint must pass cert.
    tt=[(c.pt()[1] if isinstance(c,I) else float(c),k,float(r)) for c,k,r in zterms(b)]
    qa=(CH(F(61))+value(zterms(b),F(61))/61).pt()[1]
    def hf(v,L):
        return L**(j+6)*(qa*approx_exp(61-v) + sum(
            c*v**(k-1)*approx_exp(-r*v)*(1+1/(v*(1-r-2/61))) for c,k,r in tt))
    u,w=lo,hi
    while w-u>1:
        m=(w+u)//2;v=m/100
        if hf(v-1,v)+2.07*hf(v,v)<float(sl(F(m,100))):w=m
        else:u=m
    for m in range(w,hi+1):
        v=F(m,100)
        if cert(v):return v
    raise ArithmeticError((b,j,lo,hi))

def extend():
    # More terms in the Li barrier; direct recomputation, not asymptotic fitting.
    m,a=48,61
    kk=F(9,8)*F(fac(m+1),1-F(m+2,a))
    u=F(a); p={k+1:fac(k) for k in range(m+1)}; p[m+2]=kk
    bot=sum(F(c,u**n) for n,c in p.items() if n<m+2)
    ser=sum(u**k/(k*fac(k)) for k in range(1,261))
    f=(I(F('.57'),F('.59'))+log(a)+I(ser,ser+2*u**261/(261*fac(261))))*e(-u)
    assert I(bot).lt(f) and f.lt(bot+kk/u**(m+2))
    dz={n:F(0) for n in range(2,2*m+5)}
    for n in range(2,m+3):
        dz[n]+=sum(fac(k)*comb(n-2,k) for k in range(n-1))
    for i in p:
        for j in p:dz[i+j]-=p[i]*p[j]
    assert all(dz[n]==coefficient(n) for n in range(2,m+3))
    assert all(dz[n]>0 for n in range(6,m+3))
    def sx(j,v):
        N=j+7
        assert N<=m+2
        return dz[N]+sum(c*v**(N-n) for n,c in dz.items() if n>N and c<0)
    def test(b,j,v):
        assert (j+6)/v+1/(v-1)<F(1,8)
        return (scaled_pi(b,v-1,v,j)+F('2.07')*scaled_pi(b,v,v,j)).lt(sx(j,v))
    for b in (b0,b1):
        print('R new higher profiles 17..43',str(b),
            [str(suggest(b,j,lambda v:sx(j,v),55000,220000,lambda v:test(b,j,v))) for j in range(17,44)],flush=True)
    fb=[16,24,32,43]
    for b in (b0,b1):
        a=(F(61) if b==b0 else F(200))
        t=(((F(1,25),2,1-b),(2,0,1-b),(3,2,F(1,2)),(119,0,F(1,2))) if b==b0
            else ((F(1,64),2,1-b),(2,0,F(1,2))))
        def direct_ok(v):
            assert v-1>=a and (j+6)/v+1/(v-1)<F(1,8)
            return (scaled(b,v-1,v,j,a,t)+F('2.07')*scaled(b,v,v,j,a,t)).lt(sx(j,v))
        ans=[]
        for j in fb:ans.append(str(real_search(direct_ok,54000,220000)))
        print('R higher density-free',str(b),fb,ans,flush=True)

def short_m(a,z,eta):
    # CH2 psi (or literal finite RH), sharper signed primitive, and G.
    # All L>=39; endpoints l,r below are exact rationals.
    a,z,eta=map(F,(a,z,eta))
    assert a>=39 and (5*10**6*e(-F(2,5)*39)).lt(1)
    opts=[]
    for T in (10**7,10**8,10**9,10**10,10**11,10**12,T0):
        assert I(max(T,10**9)).lt(e(F(39)))
        pairs=ch_terms(T)
        opts.append((pairs[0][0],pairs[1][0]-2))
    opts.append((A,114))
    while a<z:
        r=min(a+F(1,16),z)
        ends=[r*r*aa+a*a*cc*e(-a/2) for aa,cc in opts]
        if r<=58:
            ends.append(a**4*e(-a/2)/(8*PI))
        m=(1+1/a)*a*a*(6*e(-a/2)+F(400,H)*e(-a/8))
        g=a*a*(4*e(-a/2)+10*e(-2*a/3))
        J=pick(ends)+m+g # upper bound for L^2 times common numerator
        den=1-J/a**3
        assert I(0).lt(den)
        if not (J/den).lt(eta):return a,r
        a=r
    return None

def comparison():
    from source_rows import compare,extract
    v=F('168.9')
    compare(extract(),v)
    # All explicit B0 log rows: sufficient witnessed lower bound at their
    # active left endpoint, and |(log L^-2)'| < 1/8 beyond it.
    old=[(201,8),(240,10),(278,12),(355,16),(431,20),(507,24),
         (202,8),(240,10),(279,12),(356,16),(432,20),(508,24)]
    new=[('200.12',8),('238.90',10),('277.57',12),('354.45',16),('430.83',20),('506.83',24)]
    for a,k in old+new:
        w=max(v,F(a))
        assert (log(F('.0039'))-w/8).lt(-k*log(10)-2*log(w))
    for eta in ('.2','.05','.01','.001','1e-6','1e-7'):
        assert (log(F('.0039'))-v/8).lt(log(F(eta))-2*log(v))
    for c in (I(F('.011')),I(F('.0107')),zterms(b0)[-1][0]):
        assert I(F('.0039')).lt(c*(1-e(-F('.003')*v)))
    for d,q in ((F(0),F('1.04e-12')),(F(1,8),F('.0039'))):
        assert (zm(b1,v)*e(-(F(5,32)-d)*v)).lt(F('.99')*q)
        assert (2*(4*e(-(F(1,2)-d)*v)+10*e(-(F(2,3)-d)*v))).lt(F('.001')*q)
        assert (F(435)*direct_pi(F(435))*e(435*d)).lt(F('.99')*q)
    for a,c0,c1 in ((160,'.02232','.3148'),(250,'.01594','.2230'),(400,'.01342','.1874')):
        assert (F(c1)*e(-F(a,32))).lt(F(c0))
    print('All-ray comparison at 168.9; table-free pi proxy comparison at v=435',flush=True)

def main():
    anchors()
    assert e(F('43.74')).lt(10**19)
    for j,a in [(0,'30.75'),(1,'34.4'),(2,'38.52')]:
        assert early(F(a),F('43.74'),j=j,step=F(1,96)) is None
        print('B0 early profile interval',j,a,'43.74',flush=True)
    assert early(F('43.74'),F('47.5'),j=0,step=F(1,128)) is None
    print('B0 F0 bridge to existing ray passed',flush=True)
    fail=early(F('43.74'),F('47.5'),j=1,step=F(1,128))
    assert fail is not None
    print('F1 bridge failed (bound test only)',tuple(map(str,fail)),flush=True)
    for a,z,k in [('52.9',170,6),('58.3',215,7),('64.4','97.6',8)]:
        assert short_m(a,z,F(1,10**k)) is None
        if k<8:
            v=F(z)
            assert (zm(b0,v)*v*v*e(-v/8)).lt(F(1,10**k))
        print('B0 short M cells',a,z,k,flush=True)
    bcoef={b0:('.02232','.01594','.01342'),b1:('.3148','.2230','.1874')}
    for b in (b0,b1):
        for v,c in zip((160,250,400),bcoef[b]):
            assert zm(b,F(v)).lt(F(c))
        print('M old/new sharp coefficients',b,[(mc(b,F(v)).pt(),zm(b,F(v)).pt()) for v in (160,250,400)],flush=True)
        ar=[str(real_search(lambda v:(zm(b,v)*v*v*e(-(1-b)*v)).lt(F(1,10**k)),16000,53000)) for k in (8,10,12,16,20,24)]
        print('M new log onsets',b,ar,flush=True)
    for b in (b0,b1):
        def rtest(j,v):
            assert (j+6)/v+1/(v-1)<F(1,8)
            return (scaled_pi(b,v-1,v,j)+F('2.07')*scaled_pi(b,v,v,j)).lt(slack(j,v))
        print('R new decimal onsets 2..16',b,[str(suggest(b,j,lambda v:slack(j,v),17000,72500,lambda v:rtest(j,v))) for j in range(2,17)],flush=True)
    d=1-b1
    c=F('.015625000000005')
    assert product_bound(F(200),d,F(1,64),2).lt(c)
    assert (c*435**2*e(-F(435,32))).lt(F('.99')*F('.0039'))
    print('M direct D02 tighter coefficient',str(c),'and beats old B0 envelope from 435',flush=True)
    a=F(160)
    c0=F('.040079')
    assert product_bound(a,1-b0,F(1,25)+2/a**2+(3+119/a**2)*e(-F(3,8)*a),2).lt(c0)
    for b,C,start in [(b0,c0,160),(b1,c,200)]:
        d=1-b
        ans=[str(real_search(lambda v:(C*v**4*e(-d*v)).lt(F(1,10**k)),100*start,70000))
            for k in (8,10,12,16,20,24)]
        print('M density-free matched log onsets',str(b),ans,flush=True)
    comparison()
    extend()
if __name__=='__main__':main()
