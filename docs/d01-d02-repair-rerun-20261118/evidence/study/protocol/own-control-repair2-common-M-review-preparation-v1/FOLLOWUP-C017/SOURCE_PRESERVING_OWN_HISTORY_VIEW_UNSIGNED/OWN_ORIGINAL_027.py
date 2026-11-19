"""Ordinary interval examples from the additive portfolio, not all executables."""
from repair_spectral import *
from repair_r import margin_new,POS,DD,cost
from evaluate import evaluate,r_profile
from mertens import prime_powers
from pathlib import Path
from sys import argv
import json
from functools import lru_cache

PTH=Path(__file__).resolve().parent
J=json.loads((PTH/'repair_portfolio.json').read_text())

@lru_cache(None)
def newE(cap,L,R):
    u=I(L,R)
    v=sec(u,cap)
    if cap==newcap: v=mini(v,*(sec(u,cap,h) for h in WINS))
    return v

def r_augment(u,cap):
    r=r_profile(u,cap)
    if r is None: return None
    # Known terminal strict sign on log x>=25.
    r=maxi(r,0)
    for k,m,L,_ in J['ramanujan_early_k_m_current_previous']:
        k=int(k)
        if u.l>=D(L):
            p=horner(d[4:k],1/u)+I(m)/u**(k-4)
            r=maxi(r,p)
    if u.l>=141:
        for high in (False,True):
            r=maxi(r,margin_new(u.l,cap,4,high) if u.l==u.r else
                    u**4*(horner((POS if high else dNplus)[4:],1/u)
                          -cost(u,cap,high)))
        for k,m,b,c in J['ramanujan_full_k_coefficient_B0_D02']:
            if u.l>=D(c if cap==newcap else b):
                k=int(k)
                r=maxi(r,horner(DD[4:k],1/u)+I(m)/u**(k-4))
        for L,k,b,m in J['ramanujan_fixed_L_k_800b_m']:
            if u.l>=D(L) and cap==int(b):
                k=int(k)
                r=maxi(r,horner(d[4:k],1/u)+I(m)/u**(k-4))
        # Refined pointwise R1, not just the cheaper continuous tail.
        def widths(v):
            pp=p_err(v,cap)
            e=newE(cap,v.l,v.r)+6*primitive(v,cap)/v+17000*v*ef(1,v)
            return mini(pp[0],e-I('.988')*ef(I('.5'),v)),mini(pp[1],e+powterm(v))
        def normV(v): return v*ef(1,v)*vintegral(v)
        r=maxi(r,u**4*(u/(u-1)*(normV(u-1)-widths(u-1)[1])-
                      (normV(u)+widths(u)[0])**2))
    return r

def m_augment(u,cap,x=None):
    if x is not None and x<2:
        from repair_finite import normalizers
        g,M,B=normalizers()
        w=g.exp()*u
        return [maxi(z,-z) for z in (w-1,1/w-1,-u.ln()-M,-u+B)]
    v=evaluate(u,cap,x)
    for c,*on in J['mertens_common_C_P_Q_reciprocal_weighted_onset']:
        for i,L in enumerate(on):
            if (x is not None and x>=D(L)) or u.l>=I(L).ln().r:
                v[i]=mini(v[i],I(c)/u**(2 if i==3 else 3))
    a=1-I(cap)/800
    for L,b,c in J['mertens_power_L_B0_D02']:
        C=c if cap==newcap else b
        if C and u.l>=D(L):
            z=I(C)*ef(a,u)
            v=[mini(w,z if i==3 else z/u) for i,w in enumerate(v)]
    if u.l>=140:
        W=newE(cap,u.l,u.r)+primitive(u,cap)
        S=primitive(u,cap)
        Z=W/u+S/u**2
        lo1,hi1,lo0,hi0,ld,hd=prime_powers(u)
        n,p=Z-ld,Z+hd
        bs=(maxi(-expm1(-p),expm1(n)),maxi(-expm1(-n),expm1(p)),
            maxi(Z-lo0,Z+hi0),maxi(W-lo1,W+hi1))
        v=[mini(i,j) for i,j in zip(v,bs)]
    return v

if __name__=='__main__':
    f,s=argv[1:]
    x=I(s)
    assert f in ('log','x') and x.l>(0 if f=='log' else 1)
    u=x if f=='log' else x.ln()
    assert f=='x' or u.l>LN2.r
    for cap in (basecap,newcap):
        print('B0' if cap==basecap else 'D02')
        print('M upper endpoints',[v.r for v in m_augment(u,cap,x.l if f=='x' else None)])
        r=r_augment(u,cap)
        if r is not None: print('R lower endpoint in x^2/L^6 units',r.l)
