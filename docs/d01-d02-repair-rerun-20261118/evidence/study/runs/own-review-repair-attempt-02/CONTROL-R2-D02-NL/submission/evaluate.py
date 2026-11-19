"""Evaluate proved upper/lower profiles at a decimal log or x argument."""
from mertens import *
from pathlib import Path
from sys import argv
import json
def evaluate(u,cap,exact_x=None):
    data=json.loads(Path(__file__).with_name('portfolio.json').read_text())
    vals=list(combined(u,cap))
    powers=(3,3,3,2)
    for i,x,c in data['mertens_finite_x']:
        if (exact_x is not None and exact_x>=D(x)) or u.l>=I(x).ln().r:
            vals[i]=mini(vals[i],I(c)/u**powers[i])
    for L,c in data['mertens_log_onsets']:
        a=I(10**19).ln() if L=='log(10^19)' else I(L)
        if u.l>=a.r: vals=[mini(z,I(c)/u**k) for z,k in zip(vals,powers)]
    for L,c0,c1 in data['mertens_power_log_onsets']:
        c=c1 if cap==newcap else c0
        if c and u.l>=L:
            a=1-I(cap)/800
            vals=[mini(z,I(c)*ef(a,u)/(u if k==3 else 1)) for z,k in zip(vals,powers)]
    if exact_x is not None and exact_x<=25*10**6:
        from finite_zoom import normalizers
        from finite_mertens import sieve
        g,M,B=normalizers()
        a,b,q=I(),I(),I(1)
        for p,s in enumerate(sieve(max(2,int(exact_x)))):
            if not s or p>exact_x:continue
            a+=I(1)/p;b+=I(p).ln()/p;q*=I(p)/(p-1)
        q=q/(g.exp()*u)
        vals=[mini(z,maxi(w,-w)) for z,w in zip(vals,(1/q-1,q-1,a-u.ln()-M,b-u+B))]
    return vals

def r_profile(u,cap):
    if u.l<25: return None
    e,dn=p_err(u,cap);e1,dn1=p_err(u-1,cap)
    def f(v): return v*ef(1,v)*vintegral(v)
    v=u**4*(u/(u-1)*(f(u-1)-dn1)-(f(u)+e)**2)
    return maxi(v, margin(u,cap,4))       # scaled by L^6/x^2; lower endpoint is supported.

if __name__=='__main__':
    f,x=argv[1:]
    z=I(x)
    assert f in ('log','x') and (z.l>0 if f=='log' else z.l>1)
    u=z if f=='log' else z.ln()
    assert u.l>=LN2.r or f=='x'
    for cap in (basecap,newcap):
        if f=='x' and z.r<2:
            from finite_zoom import normalizers
            g,M,B=normalizers()
            ep=g.exp()*u
            vals=[maxi(w,-w) for w in (ep-1,1/ep-1,-u.ln()-M,-u+B)]
        else:
            vals=evaluate(u,cap,z.l if f=='x' else None)
        print(('B0' if cap==basecap else 'D02'),'M upper endpoints:',[v.r for v in vals])
        r=r_profile(u,cap)
        if r is not None: print('R/(x^2/L^6) lower endpoint:',r.l)
