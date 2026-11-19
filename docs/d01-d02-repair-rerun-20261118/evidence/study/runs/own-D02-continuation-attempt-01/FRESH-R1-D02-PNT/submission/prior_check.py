"""Directed 52-decimal interval checks, Python 3.10 standard library."""
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from math import factorial as fac, comb
import sys
BASIC='--basic' in sys.argv
lo=Context(prec=52,rounding=ROUND_FLOOR)
hi=Context(prec=52,rounding=ROUND_CEILING)
rn=Context(prec=52,rounding=ROUND_HALF_EVEN)
class I:
    def __init__(self,a,b=None):
        if isinstance(a,I):
            self.a,self.b=a.a,a.b
        else:
            self.a,self.b=D(a),D(a if b is None else b)
        assert self.a<=self.b
    def __add__(a,b):
        b=I(b);return I(lo.add(a.a,b.a),hi.add(a.b,b.b))
    __radd__=__add__
    def __neg__(a):return I(a.b.copy_negate(),a.a.copy_negate())
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b); ps=[(x,y) for x in (a.a,a.b) for y in (b.a,b.b)]
        return I(min(lo.multiply(x,y) for x,y in ps),max(hi.multiply(x,y) for x,y in ps))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.a*b.b>0
        return a*I(lo.divide(D(1),b.b),hi.divide(D(1),b.a))
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,n):
        assert isinstance(n,int) and n>=0
        if n==0:return I(1)
        if n%2==0:
            c=a**(n//2);return c*c
        return a*(a**(n-1))
    def exp(a):return I(rn.next_minus(rn.exp(a.a)),rn.next_plus(rn.exp(a.b)))
    def ln(a):
        assert a.a>0
        return I(rn.next_minus(rn.ln(a.a)),rn.next_plus(rn.ln(a.b)))
    def upper(a):return I(a.b)
    def lower(a):return I(a.a)
    def __repr__(a):return f'[{a.a},{a.b}]'
def imin(*args):return I(min(v.a for v in args),min(v.b for v in args))
def atan(x):
    s=I(0)
    for k in range(50): s+=(-1)**k*x**(2*k+1)/(2*k+1)
    return s+I(0,(x**101/101).b)
pi=16*atan(I(1)/5)-4*atan(I(1)/239)
H=3000175332800
def q(L):
    if BASIC: return I('.005')*L**2
    return (I('.01057')*L/(L-92)+I('.005')*L**2*(-I('.075')*L).exp()
      +(I('.01')*L**2+118)*(-3*L/8).exp()+I('2.091')*L*(-L/8).exp())
def Ch(L):
    t=imin(I(H),2*pi*pi*(L/2).exp()/L)
    v=(t/(2*pi)).ln()
    return pi/(t-1)+pi*pi/(3*t*t)+(v*v/(2*pi)-v/(6*pi))*(-L/2).exp()
def Gas(L):
    return pi/(3*10**12)+I('113.67')*(-L/2).exp()
def df(L):
    return I('.094')*(-L/2).exp()+I('3e-12')*(-L/8).exp()+2*(-L).exp()
def pierr(L,side,zone):
    # zone is an interior representative; grid has all breakpoints.
    if side==+1 and zone<D('39.47'): return I(0)
    b=imin(Ch(L),Gas(L))
    if zone>=(200 if BASIC else 110): b=imin(b,q(L)*(-L/8).exp())
    corre= -(-L/2).exp() if side==+1 else I('1.2551')*((-L/2).exp()+2*L*(-2*L/3).exp())
    v=(b+corre)/L+I('.376')*(-L/2).exp()/L**2+I('12e-12')*(-L/8).exp()/L**2+10000*(-L).exp()
    if zone<58:v=imin(v,L*(-L/2).exp()/(8*pi))
    return v
a=[fac(i) for i in range(21)]+[5*fac(21)]
cs=[sum(a[i]*comb(j,i) for i in range(min(20,j)+1))-sum(a[i]*a[j-i] for i in range(22) if 0<=j-i<22) for j in range(43)]
assert cs[:10]==[0,0,0,0,1,14,145,1412,13985,145450]
def hp(L, coeff):
    v=I(0); z=1/L
    for c in reversed(coeff): v=c+z*v
    return v
def gap_error(L,c,coeff=a):
    u=hp(L,coeff)/L
    A=pierr(L,+1,c)
    B=pierr(L-1,-1,c-1)
    # A need not be nonnegative mathematically, but actual formula is.
    assert A.a>=0 and B.a>=0
    return L**5*B+L**6*A*(2*u+A)
def gap_frac(L,c):
    return hp(L,cs[4:])-gap_error(L,c)
def tail_eps(L):
    # Valid bound for E_pi on L>=180; the prime-power correction plus W
    # fits in 1e-8*exp(-L/8)/L.
    return q(L)+I('1e-8')
def eps_scaled(L,m):
    # L^(m+1) times Ramanujan gap loss (L>=200); U<1.04/L.
    p=tail_eps(L)
    pm=tail_eps(L-1)
    return (L**(m+5))*(-L/8).exp()*( I('1.14')*pm+I('2.081')*p)
def constants():
    assert pi.a>D('3.1415926') and pi.b<D('3.1415927')
    h=I(3*10**12).ln()
    p=I(1)/3;j=I(13)/4
    k=1-p-j/h
    f=I('11.076')*(j*h.ln()-(1-p)*h).exp()/k
    g=4*(h*h+2*h+2)/(3*10**12)
    assert (2*(f+g)).b<D('.01057')
    z=1-I(8)/15-(I(17)/5)/h
    assert z.a>0
    dr=(I(8)/3)*h+2*h.ln()+(I(8)/3+2/h)/z
    assert dr.b<92
    assert ((h-(2*pi).ln())**2/(2*pi)+I('1.8642')).b<118
    assert (((I(110)/4-I('.9'))**2/(2*pi))+I('1.8642')).b < 121
    assert (I('2.45')/(2*pi)).ln().b<D('-.9')
    if not BASIC: assert (q(I(200))).b<D('.02')
    assert ((I(1)/8+I(8)/200)**2/(2*pi)+I('1.865')/40000
            +I('2.091')*(-I(8)).exp()/200+118*(-75*I(1)).exp()/40000).b<D('.005')
    assert ((1-2*I('0.0003')-I('0.0003')/I(64000000).ln()
              -1/I(64000000).ln()-I('0.0003'))/2).a>D('.465')
    assert ((1+3*I('0.0003')+I('0.0003')/I(64000000).ln())/2+
             I(1)/64000000).b<D('.502')
    if not BASIC: assert (q(I(180))).b<D('.022')
    assert (2*(I(14).ln()+1-(2*pi).ln())/(2*pi*14)+2*(I('.4')*I(14).ln()+I('4.1'))/196).b<D('.094')
    assert (2*(h+1-(2*pi).ln())/(2*pi*3*10**12)+2*(I('.4')*h+I('4.1'))/(9*10**24)).b<D('3e-12')
    x=I(32); y=I(0)
    for j in range(1,161): y+=(x**j-(-1)**j)/(j*fac(j))
    assert (2*(x**161+1)/(161*fac(161))).b<D('1e-41')
    F=(x.ln()+y+I((-I(-1).exp()).a,I('1e-41').b))*(-x).exp()
    P=hp(x,a[:-1])/x
    U=hp(x,a)/x
    assert P.b<F.a and F.b<U.a and (hp(I(60),a)).b<D('1.04')
    assert x.exp().a>10**9 and Ch(I(34)).b <1
    assert (2*pi*pi*I(17).exp()/34).a>10**7
    assert I('39.47').exp().b<D('1.39e17') and I(58).exp().b<D('2.169e25')
    # T=e^(L/4) Perron inequalities at L=110, increasing ratios thereafter.
    T=(I(200)/8+8).exp()
    assert T.a>200 and (I(100).exp()-2-5*T).a>0
    assert (I(110)/4).exp().a>110 and (I(55).exp()-2-5*(I(110)/4).exp()).a>0
    ep=I(1).exp()
    assert ep.b<D('2.72')
    assert (I(200)/199*(I(1)/8).exp()).b<D('1.14')
    # At L>=180, discarded terms in pierr*L*exp(L/8) decrease.
    v=I(180)
    ex=I('1.2551')*((-3*v/8).exp()+2*v*(-(I(2)/3-I(1)/8)*v).exp())
    ex+=I('.376')*(-3*v/8).exp()/v+I('12e-12')/v+10000*v*(-7*v/8).exp()
    assert ex.b<D('1e-8')
    assert (tail_eps(I(200))*(-I(200)/8).exp()).b<D('.001')
    print('constants and Li calibration verified')
def grid(l,u,step):
    a=D(l); h=D(step); b=D(u)
    while a<b:
        v=min(b,a+h)
        yield I(a,v),(a+v)/2
        a=v

margins=[('36.56','0'),('36.8','.11'),('37','.20'),('40','.42'),('40.23','.5'),
         ('41','.71'),('41.15','.75'),('41.9','.9'),('42','.92'),('42.5','1')]
higher=[(1,200),(2,225),(3,258),(4,292),(5,327),(6,362),(7,398),
        (8,434),(9,470),(10,506),(11,542),(12,578),(13,615),(14,652),(15,695)]
def tail_test(c,m,v):
    # Drop the surplus coefficients except the first and all negative ones.
    L=I(v)
    assert v>=(201 if BASIC else 200) and v>8*(m+7)
    head=c[5+m]
    lower=head-sum(I(-c[j])/L**(j-m-5) for j in range(m+6,len(c)) if c[j]<0)
    assert lower.a>eps_scaled(L,m).b,(m,v,lower,eps_scaled(L,m))
def poly(n,factor):
    a=[fac(i) for i in range(n+1)]+[factor*fac(n+1)]
    return a,[sum(a[i]*comb(j,i) for i in range(min(n,j)+1))-sum(a[i]*a[j-i] for i in range(n+2) if 0<=j-i<n+2) for j in range(2*n+3)]
a30,c30=poly(30,3)
def calibrate30():
    x=I(80)
    y=sum((x**j-(-1)**j)/(j*fac(j)) for j in range(1,601))
    F=(x.ln()+y+I((-I(-1).exp()).a,I('1e-250').b))*(-x).exp()
    assert (2*(x**601+1)/(601*fac(601))).b<D('1e-250')
    assert (hp(x,a30[:-1])/x).b<F.a and F.b<(hp(x,a30)/x).a
    assert hp(I(200),a30).b<D('1.04')
    assert c30[:21]==cs[:21] and all(c>0 for c in c30[4:31])
def gaps():
    breaks=sorted(set(D(x) for x in ('36.56','36.65','39.47','43','47.05','48','58','59','60','110','111','160','190','200','201','250','300','340'))|
                  set(D(v) for v,_ in margins))
    if not BASIC: breaks=[b for b in breaks if b<=200]
    windows={m:[] for m in (2,3,4)}
    for l,u in zip(breaks,breaks[1:]):
        step='.001' if l<D('36.65') else '.005' if l<D(48) else '.025' if l<D(60) else '.25'
        for L,c in grid(l,u,step):
            e=gap_error(L,c)
            if c>=D(49) and c<D(160):
                for m in windows:
                    if (hp(L,cs[5+m:])-L**(m+1)*e).a>0:
                        a0,b0=L.a,L.b
                        w=windows[m]
                        if w and w[-1][1]==a0: w[-1]=(w[-1][0],b0)
                        else: w.append((a0,b0))
            if c>=D('47.05') and (not BASIC or c<60):
                strength=hp(L,cs[6:])-L**2*e
                assert strength.a>0,(L,strength)
            elif c>=D('42.5'):
                assert (hp(L,cs[5:])-L*e).a>0,(L,e)
            else:
                margin=max(D(v) for x,v in margins if c>=D(x))
                assert (hp(L,cs[4:])-e).a>margin,(L,margin,hp(L,cs[4:])-e)
    for m,w in windows.items():
        print('order',m,'compact windows',[(str(a0),str(b0)) for a0,b0 in w if b0-a0>=1])
    if BASIC: tail_test(cs,0,340)
    for m,v in higher:tail_test(cs,m,v+200 if BASIC else v)
    calibrate30()
    for m,v in [(16,730),(17,770),(18,810),(19,850),(20,890),(21,930),(22,970),(23,1010),(24,1050),(25,1100)]:
        tail_test(c30,m,v+200 if BASIC else v)
    print('Ramanujan compact joins and monotone tails verified')
def endpoints():
    from subprocess import check_output
    N=38358837682; A=1644673232; B=632207037
    n=[N-5,N,N+1,14111427770]
    lines=check_output(['/work/small_end',*(str(x) for x in n)]).decode().splitlines()
    assert [list(map(int,l.split())) for l in lines]==[[n[0],A],[N,A],[N+1,A],[n[-1],B]]
    e=I(1).exp()
    assert (N/e).a>n[-1] and ((N+1)/e).b<n[-1]+1
    def R(x):return e*x/x.ln()*B-A*A
    x=I(N,N+1)
    assert (e*B*(x.ln()-1)/x.ln()**2).a>66000000
    assert R(I(N)+I('.1')).b<0
    assert R(I(N)+I('.217926')).b<0 and R(I(N)+I('.217927')).a>0
    assert I('36.56').exp().b<D('1.15e16')
    print('Last real zero isolated between N+0.217926 and N+0.217927')
if __name__=='__main__':
    constants()
    gaps()
    endpoints()
