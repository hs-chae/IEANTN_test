"""Earlier real-x onsets for the two extended power rays."""
from second_finite import normalizers,sieve
from log_layer import *
from finite_joins import nxt
import re
from pathlib import Path

C={basecap:'.01239',newcap:'.22775'}
Y=500000
JOIN=nxt(Y)
def prefix():
    gamma,M,B=normalizers()
    cg=gamma.exp()
    prod,a,b=I(1),I(),I()
    bitmap=sieve(JOIN)
    prim=[p for p,bit in enumerate(bitmap) if bit]
    assert prim[-2]<Y<prim[-1]==JOIN
    right=I(2).ln()
    last={cap:[2]*4 for cap in C}
    for p,q in zip(prim,prim[1:]):
        left,right=right,I(q).ln()
        prod*=I(p)/(p-1); a+=I(1)/p; b+=left/p
        u=I(left.l,right.r)
        c=prod/cg
        def errors(t):
            return (t/c-1,c/t-1,a-t.ln()-M,b-t+B)
        v=errors(u)
        for cap,w in C.items():
            aa=1-I(cap)/800
            au=aa*u
            slopes=((au+2)*u/c-(au+1),aa*(c-u)-1,(au+1)*v[2]-1,aa*v[3]-1)
            def scale(t,i,z):
                return (aa*t).exp()*maxi(z,-z)*(1 if i==3 else t)
            for i,er in enumerate(v):
                if slopes[i].l>=0 or slopes[i].r<=0:
                    val=maxi(scale(left,i,errors(left)[i]),
                             scale(right,i,errors(right)[i]))
                else:
                    val=scale(u,i,er)
                if val.r>=D(w): last[cap][i]=q
    for cap in C:
        assert all(x<Y for x in last[cap])
        print(cap, C[cap], *last[cap],flush=True)

def join():
    assert I(17).exp().r<25000000
    src=Path(__file__).with_name('finite_run.txt').read_text()
    data=src.split('Endpoint maxima rounded upward to 0.000001')[1]
    s=next(t for t in data.splitlines() if t.startswith(str(Y)+' '))
    M=max(map(D,re.findall(r"Decimal\('([0-9.]+)'\)",s)))
    for cap,c in C.items():
        a=1-I(cap)/800
        def f(t):return I(M)/(t**2*ef(a,t))
        assert max(f(I(Y).ln()).r,f(I(17)).r)<D(c)
    print('old prime-event maxima through exp(17) join the new suffix at next prime',JOIN)

if __name__=='__main__':
    join()
    prefix()
