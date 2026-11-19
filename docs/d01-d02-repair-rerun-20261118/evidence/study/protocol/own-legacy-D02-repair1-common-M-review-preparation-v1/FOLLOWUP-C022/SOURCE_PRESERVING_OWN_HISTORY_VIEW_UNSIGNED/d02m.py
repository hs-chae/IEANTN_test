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
    Y=(F(27,100) if B==b else F(7,20))*x
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
    assert screen(F(168),c=F(7,20))*e(-a*l)<A0
    z=F(175)
    assert combined(z)<I('.244823')
    assert I('.244823')*e(-I(z)/32)<I('.00666') and I('.244823')*e(-a*I(z))<A0
    assert I('.215402')*e(-I(200)/32)<I('.01233')
    w=I(184); A=F(1,8)
    assert A0*w**2>I('3.54e-8') and A0*e(A*w)>I('.01')
    assert screen(F(184),F(7,8),c=F(7,20))*e(-A*w)>A0
    import portfolio_check as B0screen
    assert I(B0screen.spectral(F(184)).L())*e(-A*w)>A0
    assert I(B0screen.Z[-1].L())>I('.00666')
    assert I('9.22022')*I(z)*e(log(z)/2-I('.8476836')*e(log(z)/2))>I('.244823')*e(-a*I(z))
    assert a>I('.8476836')/(2*e(log(z)/2))
    assert I(200)**2/64>I('.215402')
    assert scr2(F(180))*e(-I(180)/32)<I('.00666')/I(B0screen.H.U())

def primorial(T):
    def rest(y):
        x=I(y);J,J2=smooth(y)
        return ((1+1/x)*J+2*(1/x+2/x**2)*J2
                   +I('2.000000294')*e(-(F(1,2)-a)*x)+I('2.67')*e(-(F(2,3)-a)*x)+x*e(-b*x))
    flat=lambda y:e(a*I(y))*(A0+117*e(-I(y)/2))**2
    assert 1/(2*I('.99'))+1/(2*I('.99')**2*155*(1-I('.01')/(I('.99')*155)))<1
    assert A0+117*e(-I(155)/2)<I('.01')
    assert I('.257')*e(-a*I(T))<I('.01')
    assert 3*e(-(F(1,2)-a)*I(T))+screen(T,c=F(7,20))<I('.257')
    z=maxI(maxI(flat(F(155)),flat(T))+rest(F(155)),I('.257')**2*e(-a*I(T))+rest(T))
    assert z/(1-z*e(-155*a)/155)<I('3.273e-13')
    print('primorial L*x^a scale ceiling:',z,flush=True)

def main():
    prelim()
    T=F('167.84')
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
    rows=[('59.5',0,2,'5.30e-8'),('60.98',0,2,'2.951e-8'),('59.5',0,3,'4.952e-6'),
          ('59.5',0,4,'.0008311'),('59.5',0,5,'.13950'),('59.5',0,6,'23.412'),
          ('59.5',F(1,8),0,'.001354'),('59.5',F(9,64),0,'.018643'),('59.5',a,0,'.256707')]
    for L,al,q,c in rows:
        v=convexbridge(F(L),T,al,q)
        assert q<=(a-al)*T
        v=maxI(v,combined(T)*I(T)**q*e((al-a)*I(T)))
        assert v<I(c),(L,al,q,c,v)
        print('bridge (L, alpha, q), combined upper cap',L,al,q,v,flush=True)
    levels=[(168,'.256418'),(170,'.252899'),(175,'.244823'),(180,'.237637'),
                (190,'.225412'),(200,'.215402'),(225,'.196863'),
                (250,'.184130'),(300,'.167809'),(400,'.151060'),
                (600,'.137363'),(1000,'.129304')]
    more=[(173,'.248838'),(175,'.245767'),(181,'.238698'),(185,'.232384'),
          (195,'.221577'),(205,'.212654'),(228,'.195899'),
          (204,'.213'),(180,'.239'),(1000,'.128081')]
    for L,c in levels+more:
        v=combined(F(L));assert v<I(c),(L,v,c)
        print('D02 power ray, L and bound',L,c,v,flush=True)
    for L,c in [(168,'.261492'),(175,'.249146'),(180,'.241556'),(200,'.218341'),(250,'.186256')]:
        assert spec(F(L),dusart_only=True)<I(c)
    for l,al,q,c in [('168',0,2,'2.944e-8'),('168',0,3,'4.935e-6'),
                     ('168',0,4,'.0008274'),('168',0,5,'.13872'),('168',0,6,'23.257'),
                     ('169',F(1,8),0,'.001323'),('171',F(9,64),0,'.018165'),
                     ('173',a,0,'.249412')]:
        assert q<=(a-al)*F(l)
        v=combined(F(l))*I(l)**q*e((al-a)*I(l))
        assert v<I(c),(l,al,q,c,v)
        print('fixed-target later ray',l,al,q,v,flush=True)
    finitejoins()
    tape=Path('repair_tape.txt').read_text()
    base=Path('d02finite_results.txt').read_text()
    p,q=tape.split('New shape:'); u,v=q.split('k/100')
    pp,qq=base.split('New shape:'); uu,vv=qq.split('k/100')
    assert p==pp and v==vv
    rows=lambda z:dict((int(k),tuple(map(int,v.split()))) for k,v in
                           (ln.split(':') for ln in z.splitlines()[1:]))
    new,prior=rows(u),rows(uu)
    assert all(new[k]==prior[k] for k in prior)
    for k in sorted(set(new)-set(prior)):
        assert k>=1354 and all(75000000<=t<250000000 for t in new[k])
        print('new finite tape: coefficient units 1e-6, (P/Q,S,V)',k,new[k],flush=True)
    elementary_comparison()
    primorial(T)

if __name__=='__main__': main()
