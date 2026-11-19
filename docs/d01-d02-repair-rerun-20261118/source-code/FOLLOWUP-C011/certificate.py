"""Reproducible interval checks. Run with /usr/bin/python3.10 certificate.py."""
from intervals import I, F, PI, log, exp
from math import factorial as fac, comb
from functools import lru_cache
A=F('1.048e-12')
H=3*10**12
b0,b1=F(7,8),F(27,32)
m=24
a=31
K=F(fac(m+1),1-F(m+2,a))
@lru_cache(None)
def e(v): return exp(I(v))
def fm(v):
    return sum(F(fac(j),v**(j+1)) for j in range(m+1))
def fu(v): return fm(v)+K/v**(m+2)
def coefficient(n):
    return sum(fac(k)*comb(n-2,k)-fac(k)*fac(n-2-k) for k in range(n-1))
# Lower polynomial for scaled li-gap, coefficients indexed by unscaled exponent n.
p={k+1:fac(k) for k in range(m+1)};p[m+2]=K
D={n:F(0) for n in range(2,2*m+5)}
for n in range(2,m+3):
    D[n]+=sum(fac(k)*comb(n-2,k) for k in range(n-1))
for i in p:
    for j in p:D[i+j]-=p[i]*p[j]
def slack(j,l,r=None):
    # Lower bound for (li-gap normalized - truncated profile j)*L^(j+1).
    N=j+7
    if r is None: return D[N]+sum(c*l**(N-n) for n,c in D.items() if n>N and c<0)
    return D[N]+sum(c*(r if c>=0 else l)**(N-n) for n,c in D.items() if n>N)
def Z(s):
    h=log(H);q=5-2*s;d=(8*s-5)/3
    return 24*exp(q*log(h)-d*h)/(d-q/h)+10*(h*h+2*h+2)/H
@lru_cache(None)
def density(b):
    pts=sorted(set([F(3,4)+F(i,2000) for i in range(251) if F(3,4)+F(i,2000)<b]+[b]+([b1] if b==b0 else [])))
    us=[Z(s) for s in pts[:-1]]+[I(0)]
    assert all(us[j+1].lt(us[j]) for j in range(len(us)-1))
    return tuple((us[j]-us[j+1],0,1-pts[j+1]) for j in range(len(us)-1))
@lru_cache(None)
def ts(b):return ((F(1,25),2,F(1,4)),(2,0,F(1,4)),(3,2,F(1,2)),(119,0,F(1,2)))+density(b)
def value(terms,v):
    return sum(c*v**k*e(-d*v) for c,k,d in terms)
def transfer(terms,a,v,anchor):
    return anchor*e(a-v)+sum(c*v**(k-1)*e(-d*v)*(1+1/(v*(1-d-F(2,a)))) for c,k,d in terms)
def pick(seq):return min(seq,key=lambda t:t.h)
def fRH(v):
    # Below 43: dominated Büthe bound (PT PNT p.8); from 43:
    # literal FiniteRH Cor.1, with two logs.
    assert 24<=v<=58
    return v**(1 if v<43 else 2)*e(-v/2)/(8*PI)
@lru_cache(None)
def ch_terms(T):
    w=log(T/(2*PI)); aa=PI/(T-1)+PI**2/(3*T*T)
    cc=w*w/(2*PI)-w/(6*PI)+2
    return ((aa,0,F(0)),(cc,0,F(1,2)))
@lru_cache(None)
def TCH(T,v0):
    terms=ch_terms(T)
    return terms, fRH(v0)+value(terms,v0)/v0
@lru_cache(None)
def CH(v,T=0):
    if T:
        a=F(24 if T<=10**10 else 29)
        t,c=TCH(T,a)
    else:
        a=F(50)
        t=((A,0,F(0)),(116,0,F(1,2)))
        c=fRH(a)+value(t,a)/a
    return transfer(t,a,v,c)
@lru_cache(None)
def dense_pi(b,v):
    a=F(61)
    t=ts(b)
    return transfer(t,a,v,CH(a)+value(t,a)/a)
@lru_cache(None)
def pure_c(b,a=F(160)):
    # Domination on [a,infty) follows by differentiating scaled terms.
    return value(tuple((c,k,d-(1-b)) for c,k,d in ts(b)),a)
@lru_cache(None)
def pure_pi(b,v):
    a=F(160)
    t=((pure_c(b),0,1-b),)
    return transfer(t,a,v,CH(a)+value(t,a)/a)
@lru_cache(None)
def err(v,b,up):
    if up and v<=F('39.3'): return I(0)
    r=[CH(v,T) for T in (100000000,200000000,300000000,10**9,3*10**9,10**10,10**11,10**12)]
    if v<=58:r.append(fRH(v))
    if v>=50:r.append(CH(v))
    if v>=160:r.append(pure_pi(b,v))
    return pick(r)
def finite(a,z,b,j=None,margin=None,step=F(1,32)):
    # [a,z], left estimates must be available throughout each cell;
    # split the upper signed-pi cutoff and both finite-RH cutoffs safely.
    a,z=F(a),F(z)
    while a<z:
        cuts=[x for x in (F('39.3'),F(43),F(44),F(58),F(59)) if a<x]
        r=min([a+step,z]+cuts)
        pu=err(a,b,True) if r<=F('39.3') else err(a,b,False)
        # When a cell extends beyond v=58 a finite RH estimate must not be used.
        def safe(v,end,u):
            if v==58 and end>58:
                return pick([CH(v)]+[CH(v,T) for T in (10**10,10**11,10**12)])
            return err(v,b,u)
        if a==58 and r>58:pu=safe(a,r,False)
        pl=safe(a-1,r-1,False)
        loss=(r**5)*(pl+F('2.07')*pu)
        if j is None:
            low=1+sum(D[n]*(r if D[n]>=0 else a)**(6-n) for n in range(7,max(D)+1))
            if not loss.lt(low-margin):return (a,r,loss.pt(),float(low-margin))
        else:
            if not (loss*r**(j+1)).lt(slack(j,a,r)):
                return (a,r,(loss*r**(j+1)).pt(),float(slack(j,a,r)))
        a=r
    return None
def tail(b,j,a):
    a=F(a)
    assert (j+6)/a+1/(a-1)<F(1,8)
    up=a**(j+6)*(dense_pi(b,a-1)+F('2.07')*dense_pi(b,a))
    return up.lt(slack(j,a)), up.pt(),float(slack(j,a))
def search(b,j,start=170):
    for a in range(start,1201):
        t=tail(b,j,a)
        if t[0]:return a,t
def anchors():
    assert I(10**10).lt(e(F(24))) and I(10**12).lt(e(F(29))) and I(10**9).lt(e(F(24)))
    u=F(24)
    assert I(2657).lt(e(u)) and e(F(43)).lt(10**19)
    assert ((F('1.95')+F('3.9')/u+F('19.5')/u**2)/u+2*e(-u/2)).lt(u/(8*PI))
    assert e(F(58)).lt(F('2.169e25'))
    assert e(F(50)).lt(F('2.169e25'))
    assert e(F('39.3')).lt(F('1.2e17'))
    assert PI.lt(F('3.141593')) and I(F('3.141592')).lt(PI)
    assert (PI/H).lt(A)
    hh=log(H/(2*PI))
    assert (hh*hh/(2*PI)+F('1.8642')).lt(117)
    assert I(F('1.04e-12')).lt(PI/(T0-1))
    # Euler constant bracket from H_100-log 100-1/100 <= gamma <= H_100-log 100.
    hn=sum(F(1,k) for k in range(1,101))-log(100)
    assert I(F('.57')).lt(hn-F(1,100)) and hn.lt(F('.59'))
    u=F(a)
    ser=sum(u**k/(k*fac(k)) for k in range(1,181))
    f=(I(F('.57'),F('.59'))+log(a)+I(ser,ser+2*u**181/(181*fac(181))))*e(-u)
    assert I(fm(u)).lt(f) and f.lt(fu(u)), (fm(u),f.pt(),fu(u))
    assert all(D[n]==coefficient(n) for n in range(2,m+3))
    assert 37*fu(F(37))<F('1.03')
    # global bound P(L)<.01/L: for v>=37 use T=2e8, v P(v)
    # decreased exponential factors, and decreasing constant-term multiplier.
    assert (37*CH(F(37),200000000)).lt(F('.01'))
T0=3000175332800
def no_density(v,b=b0):
    a=F(61)
    d=1-b
    terms=((F(1,25),2,d),(2,0,d),(3,2,F(1,2)),(119,0,F(1,2)))
    return transfer(terms,a,v,CH(a)+value(terms,a)/a)
def direct_pi(v):
    a=F(200)
    terms=((F(1,64),2,F(5,32)),(2,0,F(1,2)))
    return transfer(terms,a,v,CH(a)+value(terms,a)/a)
def alt_rates():
    for j,z0,z1 in [(1,325,255),(2,355,290),(4,440,365),(8,630,495)]:
        result=[]
        for efun,z in [(no_density,z0),(direct_pi,z1)]:
            for n in range(201 if efun==direct_pi else 160,z):
                v=F(n)
                if (j+7)/(v-1)>=F(1,8): continue
                w=v**(j+6)*(efun(v-1)+F('2.07')*efun(v))
                if w.lt(slack(j,v)):
                    result.append(n);break
        assert len(result)==2
        print('Density-free profile',j,result,flush=True)
def fallback():
    # CH2 branch alone on [60,280]. Derivative-free interval test.
    for k in range(4*60,4*280):
        l,r=F(k,4),F(k+1,4)
        assert (r**6*(CH(l-1)+F('2.07')*CH(l))).lt(slack(0,l,r))
    # For v>=280 the following normalized loss decreases by differentiation.
    for b in (b0,b1):
        l=F(280)
        assert (l**6*(no_density(l-1,b)+F('2.07')*no_density(l,b))).lt(slack(0,l))
def mertens_checks():
    W=lambda v,aa,cc: aa+(cc+4)*e(-v/2)+10*e(-2*v/3)
    J=lambda v,aa,cc:(2*aa+(cc+4+2*cc/v)*e(-v/2)+10*e(-2*v/3))/v
    def test(l,r,eta):
        for T in (0,10**7,10**8,10**9,10**10,10**11,10**12,T0):
            if T:
                if not I(max(T,10**9)).lt(e(l)):continue
                term=ch_terms(T)
                aa,cc=term[0][0],term[1][0]-2
            else:aa,cc=A,114
            z=J(l,aa,cc)
            if ( (2*aa*r*r + (cc+4+2*cc/l)*l*l*e(-l/2)+10*l*l*e(-2*l/3))/(1-z)).lt(eta):return True
        return False
    def bound_at(b,v):
        d=1-b
        P=pure_c(b,v)
        mass=(4+6*(v*v+4*v+8))*e(-(F(1,2)-d)*v)+I(F(400,H))
        powers=4*e(-(F(1,2)-d)*v)+10*e(-(F(2,3)-d)*v)
        zz=P+(1+1/v)*mass+powers
        return zz/(1-zz*e(-d*v)/v)
    for b,cs in ((b0,('.0263','.0182','.0151')),(b1,('.427','.292','.241'))):
        for v,c in zip((160,250,400),cs):
            assert bound_at(b,F(v)).lt(F(c))
    rates=[('23.25','.2',160),('26.5','.05',160),('30.25','.01',160),('36.25','.001',160),
           (53,'.000001',170),(62,'.0000001',215)]
    for a,eta,end in rates:
        a,eta=F(a),F(eta)
        assert all(test(F(j,4),F(j+1,4),eta) for j in range(int(a*4),end*4))
        assert (bound_at(b0,F(end))*end**2*e(-F(end,8))).lt(eta)
        print("Mertens uniform log-rate onset",str(a),str(eta),flush=True)
    for k,want in [(8,[202,178]),(10,[240,209]),(12,[279,240]),(16,[356,301]),(20,[432,362]),(24,[508,422])]:
        eta=F(1,10**k)
        res=[]
        for b in (b0,b1):
            for v in range(160,650):
                v=F(v)
                if (bound_at(b,v)*v*v*e(-(1-b)*v)).lt(eta):
                    res.append(int(v));break
        assert res==want
        print("Mertens late log-rate",str(eta),res,flush=True)
    # Density-free fallback: allowance for signed integral and prime powers.
    v=F(200);d=F(5,32)
    mass=(4+6*(v*v+4*v+8))*e(-(F(1,2)-d)*v)+I(F(400,H))
    powers=4*e(-(F(1,2)-d)*v)+10*e(-(F(2,3)-d)*v)
    t=F(1,64)+((1+1/v)*mass+powers)/v**2
    assert (t/(1-t*v*e(-d*v))).lt(F('.015626'))
    # Lower bound on the B0 final density coefficient and comparisons at L=180.
    assert I(F('.011')).lt(density(b0)[-1][0])
    assert I(F('.0039')).lt(F('.011')*(1-e(-F(180,400))))
    assert (F('.427')*e(-F(5,32)*180)).lt(F('1.04e-12')*F('.99'))
    assert (F('.427')*e(-F(1,32)*180)).lt(F('.0039')*F('.99'))
    g=2*(4*e(-F(180,2))+10*e(-F(360,3)))
    assert g.lt(F('.00104e-12')) and (g*e(F(180,8))).lt(F('.0000039'))
if __name__=='__main__':
    anchors()
    fallback()
    for a,z,t in [('37.2','39.3','.06'),('39.3',42,'0'),('39.5',50,'.05'),
                  (40,50,'.25'),(41,50,'.6'),(42,50,'.84')]:
        w=finite(a,z,b0,margin=F(t))
        assert w is None
        print('early',a,z,t,w,flush=True)
    for a,z,t,step in [('37.2',43,'.005','.001'),('39.4',43,'.05','.01'),
                       ('39.9',43,'.25','.01'),('40.9',43,'.6','.01'),
                       ('41.9',43,'.84','.01')]:
        assert finite(a,z,b0,margin=F(t),step=F(step)) is None
    for j,a,z,step in [(0,'42.8',60,'.02'),(1,'47.5',48,'.02'),(2,53,120,'0.125'),
                       (3,58,91,'0.125'),(4,64,'71.5','0.125')]:
        assert finite(a,z,b0,j=j,step=F(step)) is None
    print('Improved early constants, F0 and F1 refinements, and finite F2/F3/F4 windows passed',flush=True)
    assert finite(43,60,b0,j=0,step=F(1,16)) is None
    assert finite(48,170,b0,j=1,step=F(1,8)) is None
    assert finite(48,180,b1,j=1,step=F(1,8)) is None
    for b,aa in [(b0,[280,192,223,256,290,325,360,396,432,468,504,540,576,613,649,685,722]),
                 (b1,[280,180,190,214,240,266,292,318,345,372,399,426,453,480,507,535,562])]:
        for j,v in enumerate(aa):
            assert tail(b,j,v)[0],(b,j,v,tail(b,j,v))
        print('tail onsets',str(b),aa,flush=True)
    print('pure constants at 160, 250, 400',[(str(b),[pure_c(b,F(a)).pt() for a in (160,250,400)]) for b in (b0,b1)],flush=True)
    alt_rates()
    mertens_checks()
