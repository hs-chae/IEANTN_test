"""Exact checks for the no-log Chebyshev estimates and Ramanujan upgrades."""
from functools import lru_cache
from cert import F,lni,expi,a,E,verify_mesh,poly_scaled

H=F('3e12')
L=F('28.72')
A=F(27,32)
Q=F(7,8)
COUNT=256
sig0=F(3,4)
A0=F('2.091')
QT=3*3*F('6.28')

FP=1<<112
def up(x):
    return F((x*FP)//1+1,FP)
def down(x):
    return F((x*FP)//1,FP)
@lru_cache(None)
def d(sig):
    p=F(8,3)*(1-sig)
    q=5-2*sig
    r=1-p-q/L
    assert r>0
    l3,h3=lni(3)
    ll,hl=lni(L)
    zlo,zhi=p*l3+q*ll-(1-p)*L,p*h3+q*hl-(1-p)*L
    c=F('9.8')/r
    R=103*(L**2+2*L+2)
    ll,hl=expi(-L)
    return down(c*expi(down(zlo))[0]+R*ll),up(c*expi(up(zhi))[1]+R*hl)

def pref(beta,t):
    sig=[sig0+(beta-sig0)*i/COUNT for i in range(COUNT+1)]
    norms=[d(s) for s in sig[:-1]]
    ans=norms[-1][1]
    for i in range(1,COUNT):
        hi=max(F(0),norms[i-1][1]-norms[i][0])
        ans+=hi*up(expi((sig[i]-beta)*t)[1])
    ans+=(t*t/QT+F('1.8642'))*expi((sig0-beta)*t)[1]
    ans+=A0*t*expi((F(2,3)-beta)*t)[1]
    return ans

def verify():
    assert L<lni(H)[0]
    # FKS parameters for t>=80, then by monotonicity and growth comparison.
    t=F(80)
    assert expi(t/3)[0]>t>51
    assert 5*expi(t/3)[1]+2<expi(t/2)[0]
    assert expi(t/3)[0]*F('2.45')>2*F(22,7)
    assert all(b-sig0>2/t and b-F(2,3)>1/t for b in (A,Q))
    for b,tests in [(A,[(169,'.270'),(200,'.227'),(300,'.177'),(400,'.159'),(1000,'.135')]),
                    (Q,[(187,'.014'),(200,'.013'),(300,'.0102'),(400,'.0092'),(1000,'.0079')])]:
        for t,m in tests:
            y=pref(b,F(t))
            print('density cap',str(b),t,float(y),m)
            assert y<F(m)
    assert F('.270')*expi(-(1-A)*169)[1]<a
    assert F('.014')*expi(-(1-Q)*187)[1]<a
    for key,cc,left in [('densityA',F(65),50),('densityQ',F(16),50)]:
        verify_mesh(F('48.75'),F(49),F(1,64),key,F(14))
        verify_mesh(F(49),F(250),F(1,8),key,F(14))
        assert E(F(250),F(250),7,key)<F('.5')
        l=F(left)
        while l<250:
            h=l+(F(1,32) if l<51 or 186<=l<188 else F(1,4))
            assert poly_scaled(l,h,7)-E(l,h,7,key)>cc,(key,l,h,cc)
            l=h
        # Code reuses the same proof for higher margins on subrays.
        first=F('187.5' if key=='densityA' else '218.5')
        l=first
        while l<300:
            h=l+F(1,4)
            assert poly_scaled(l,h,7)-E(l,h,7,key)>144,(key,l,h,'144')
            l=h
        assert E(F(300),F(300),7,key)<F('.5')
        l=F(190 if key=='densityA' else 220)
        while l<300:
            h=l+F(1,4)
            assert poly_scaled(l,h,7)-E(l,h,7,key)>145
            l=h
        assert E(F(300),F(300),8,key)<100
    # Small improvement even at the limiting constants of the full curve.
    assert (F(8,3)*(L+lni(3)[1])+2*lni(L)[1]
            +(F(8,3)+2/L)/(1-F(2,3)-F(7,2)/L)) < 100
    t=F(50000)
    for b,cap in [(A,F('.119')),(Q,F('.0068'))]:
        assert d(b)[1]*t/(t-100)+(t*t/QT+F('1.8642'))*expi((sig0-b)*t)[1]+A0*t*expi((F(2,3)-b)*t)[1]<cap
    print('Density and refined Ramanujan certificates passed')

if __name__=='__main__':verify()
