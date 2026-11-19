"""D02 Mertens certificates; exact directed interval arithmetic."""
from d02screen import *
from pathlib import Path
from mertens_new import scale as d01scale
from rigor import F as F_old

@lru_cache(None)
def smooth(L,alpha=a):
    x=I(L); B=1-alpha
    off=minI(I('7e-12'),scr2(L,B)) if L>=t0 else I('7e-12')
    j=I('.04620')*e(-(F(1,2)-alpha)*x)+2*e(-B*x)
    j2=I('.04620')/14*e(-(F(1,2)-alpha)*x)+2*e(-B*x)
    return j+off,j2+off/H

def combined(L,B=b):
    x=I(L); alpha=1-B
    J,J2=smooth(L,alpha)
    Y=F(7,20)*x
    v=screen(L,B,c=F(7,20))+2*(Y+1)*e(-Y)/PI+2*e(-B*x)
    z=v+J/x+2*(1/x+2/x**2)*J2+2*e(-(F(1,2)-alpha)*x)+x*e(-B*x)
    return z/(1-z*e(-alpha*x)/x)

def bz(L):
    x=I(L); U0=e(-x/2); V0=e(-x); off=I('7e-12')*e(-a*x)
    j=I('.04620')*U0+2*V0+off
    j2=I('.04620')*U0/14+2*V0+off/H
    return A0+I('115.67')*U0+(1+1/x)*j+2*(1/x+2/x**2)*j2+x*V0

def convexbridge(lo,hi,alpha=F(0),q=0):
    assert lo>=F('59.5') and 0<=q<=6 and 0<=alpha<=a
    f=lambda l:bz(l)*I(l)**q*e(alpha*I(l))
    return maxI(f(lo),f(hi))/(1-bz(lo)/I(lo))
def spec(L,B=b,dusart_only=False):
    x=I(L); alpha=1-B
    if dusart_only:
        J=I('.04620')*e(-(F(1,2)-alpha)*x)+2*e(-B*x)+I('7e-12')
        J2=J
    else:
        J,J2=smooth(L,alpha)
    z=(screen(L,B,dusart_only,c=F(7,20))+(1+1/x)*J
          +2*(1/x+2/x**2)*J2+2*e(-(F(1,2)-alpha)*x)+x*e(-B*x))
    return z/(1-z*e(-alpha*x)/x)

# Absolute comparator analytic on [lo,hi]. Used on closed cells.
def bridge(lo,hi,alpha=F(0),q=0):
    x,y=I(lo),I(hi)
    U0=e(-x/2); V0=e(-x); J,J2=smooth(lo)
    j=e(-a*x)*J; j2=e(-a*x)*J2
    z=A0+I('115.67')*U0+(1+1/x)*j+2*(1/x+2/x**2)*j2+x*V0
    return z/(1-z/x)*y**q*e(alpha*y)

def bridgecover(lo,hi,step,alpha,q):
    x,hi,step=F(lo),F(hi),F(step)
    worst=I(0)
    while x<hi:
        y=min(x+step,hi)
        worst=maxI(worst,bridge(x,y,alpha,q))
        x=y
    return worst

def lowcover(lo,hi,step,alpha,q):
    x,hi,step=F(lo),F(hi),F(step)
    worst=I(0)
    while x<hi:
        y=min(x+step,hi)
        mode=0 if y<=F('29.9') else 1 if y<=F('43.7') else 2
        assert not any(x<t<y for t in [F('29.9'),F('43.7')])
        v=I(d01scale(x,y,mode,plain=True).U())*I(y)**q*e(I(y)*alpha)
        worst=maxI(worst,v)
        x=y
    return worst

def bands(path,start,end,alpha,q):
    worst=I(0); start,end=F(start),F(end)
    join=start
    for ln in Path(path).read_text().splitlines():
        if not ln.startswith('['): continue
        ls,rs=ln[1:].split('] : ')
        aa,bb=map(int,ls.split(','))
        lb,ub=max(aa,start),min(bb,end)
        if lb>=ub:continue
        assert lb==join
        k=max(map(int,rs.split()))
        worst=maxI(worst,*(I(k)/10**9*log(x)**(q-2)*e(alpha*log(x)) for x in [lb,ub]))
        join=ub
    assert join==end
    return worst


def finitejoins():
    t=Path('d02finite_results.txt').read_text()
    assert 'N=250000000,' in t and t.index('New shape:')<t.index('k/100')
    s=t.split('New shape:')[1].split('k/100')[0].splitlines()[1:]
    for row in s:
        lev, ends=row.split(':'); c=F(lev)/10**6
        ends=list(map(int,ends.split()))
        assert c>0 and all(75000000<=k<250000000 for k in ends)
        print('finite shape/ray from (P,Q ; S ; V)',c,ends)
    assert s[0].split(':')[0]=='1324 '
    assert max(map(int,s[0].split(':')[1].split()))==180364618
    assert bands('finite20b.txt',250000000,20000000000,F(1,8),0)<I('.001323')
    assert e(F('23.7'))<20000000000 and e(F('18.42'))<100000000
    for l,r in [('23.7','29.9'),('29.9','43.7'),('43.7','59.5')]:
        assert lowcover(l,r,F(1,25),F(1,8),0)<I('.001323')
    for al,c in [(F(9,64),'.018165'),(a,'.249412')]:
        assert bands('finite26.txt',300000,100000000,al,0)<I(c)
        for l,r in [('18.42','29.9'),('29.9','43.7'),('43.7','59.5')]:
            assert lowcover(l,r,F(1,25),al,0)<I(c)
    # Old polynomial-scale threshold rows from the new tape.
    def rows(t):
        return {int(k):tuple(map(int,v.split())) for (k,v) in
                (ln.split(':') for ln in t.split('k/100')[1].splitlines()[1:])}
    for k,v in rows(t).items():
        if k>=4:
            assert all(300000<=x<250000000 for x in v)
            assert max(rows(Path('finite20b.txt').read_text())[k])<250000000
    assert F(2)*F(3)**35/fac(35)<F(1,2**56)

def elementary_comparison():
    l=I(168)
    assert combined(F(168))<I('.248838')
    assert screen(F(168),c=F(7,20))*e(-a*l)<A0
    z=F(175)
    assert combined(z)<I('.239')
    assert I('.239')*e(-I(z)/32)<I('.00666') and I('.239')*e(-a*I(z))<A0
    # In same-exponent B0 scale, the original CH2/screen/Dusart
    # bounds cannot explain the new convex bridge through 184:
    w=I(184); A=F(1,8)
    assert A0*w**2>I('3.54e-8') and A0*e(A*w)>I('.01')
    # A lower bound for either version of the baseline screen at 184
    # comes from its terminal mass and every nonnegative right bin.
    for p in [F(7,8)]:
        assert screen(F(184),p,c=F(7,20))*e(-A*w)>A0
    import portfolio_check as B0screen
    assert I(B0screen.spectral(F(184)).L())*e(-A*w)>A0
    assert I(B0screen.Z[-1].L())>I('.00666')
    # Original stretched-exponential direct branch cannot explain this
    # rate improvement: use the ratio at 175 and positive log derivative.
    assert I('9.22022')*I(z)*e(log(z)/2-I('.8476836')*e(log(z)/2))>I('.239')*e(-a*I(z))
    assert a>I('.8476836')/(2*e(log(z)/2))
    # Actual raw hypothesis and earlier historical coefficient comparisons:
    assert I(200)**2/64>I('.213')
    assert I('.213')<I('.24')
    # Separate primorial magnitude check, normalized by L*x^a.
    def prim_rest(y):
        x=I(y);J,J2=smooth(y)
        return ((1+1/x)*J+2*(1/x+2/x**2)*J2
                   +I('2.000000294')*e(-(F(1,2)-a)*x)+I('2.67')*e(-(F(2,3)-a)*x)+x*e(-b*x))
    T=F('167.656')
    flat=lambda y:2*e(a*I(y))*(A0+117*e(-I(y)/2))**2
    assert e(-(F(1,2)-a)*I(T))*3+screen(T,c=F(7,20))<I('.25')
    z=maxI(flat(F(155)),flat(T))+prim_rest(F(155))
    z=maxI(z,I('.125')*e(-a*I(T))+prim_rest(T))
    assert z/(1-z*e(-155*a)/155)<I('6e-13')
    print('primorial L*x^a scale ceilling:',z,flush=True)

def main():
    prelim()
    T=F('167.656')
    assert combined(F(155)) < I('.3')
    # Independent-of-A shortcut to the first q=2 bridge row.
    z2=lambda t:bz(t)+(I('7e-12')*e(-I(t)/8))*(1+1/I(t)+2*(1/I(t)+2/I(t)**2)/H)
    left=F('59.5'); right=F(188)
    assert maxI(z2(left)*I(left)**2,z2(right)*I(right)**2)/(1-z2(left)/I(left))<I('5.30e-8')
    import portfolio_check as old
    assert I(old.spectral(right).U())<I('.014')
    x=I(right); J=I('.04620')*e(-x/2)+2*e(-x)+I('7e-12')*e(-x/8)
    B=I('.014')*e(-x/8)+ (1+1/x)*J+2*(1/x+2/x**2)*J+2*e(-x/2)+x*e(-x)
    assert x*x*B/(1-B/x)<I('5.30e-8')
    rows=[('59.5',0,2,'5.30e-8'),('60.98',0,2,'2.944e-8'),('59.5',0,3,'4.935e-6'),
          ('59.5',0,4,'.0008274'),('59.5',0,5,'.13872'),('59.5',0,6,'23.257'),
          ('59.5',F(1,8),0,'.001323'),('59.5',F(9,64),0,'.018165'),('59.5',a,0,'.249412')]
    for L,al,q,c in rows:
        v=convexbridge(F(L),T,al,q)
        assert q<a*T
        v=maxI(v,combined(T)*I(T)**q*e((al-a)*I(T)))
        assert v<I(c),(L,al,q,c,v)
        print('bridge (L, alpha, q), combined upper cap',L,al,q,v,flush=True)
    for L,c in [(168,'.248838'),(170,'.245767'),(175,'.238698'),(180,'.232384'),
                (190,'.221577'),(200,'.212654'),(225,'.195899'),
                (250,'.184171'),(300,'.168790'),(400,'.152502'),
                (600,'.138777'),(1000,'.129304')]:
        v=combined(F(L));assert v<I(c),(L,v,c)
        print('D02 power ray, L and bound',L,c,v,flush=True)
    for L,c in [(168,'.261492'),(175,'.249146'),(180,'.241556'),(200,'.218341'),(250,'.186256')]:
        assert spec(F(L),dusart_only=True)<I(c)
    finitejoins()
    elementary_comparison()

if __name__=='__main__': main()
