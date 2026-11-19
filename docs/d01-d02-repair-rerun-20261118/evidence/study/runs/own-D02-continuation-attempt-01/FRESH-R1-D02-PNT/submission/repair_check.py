"""Repair-stage directed certificates, using check.py's standard-library intervals."""
from check import I,D,pi,Gas,df,q,poly,hp,grid,imin
from math import factorial
import sys

def imax(*v):
    return I(max(x.a for x in v),max(x.b for x in v))

h=I(3*10**12).ln()
dH=h-(2*pi).ln()
def QB(L):
    t=L/8+I('3.75')
    return (imax(I(0),(t*t-dH*dH)/(4*pi)+I('1.8642'))
        +(t*t/(2*pi)+I('1.8642'))*(-3*L/8).exp()
        +I('2.091')*(-I('4.65')).exp()*L)

def bracket(s):
    j=5-2*s
    r=1-8*(1-s)/3
    term=I(1); total=term; deriv=I(0)
    for k in range(1,5):
        term=term*(j-k+1)/(h*r)
        total+=term
        deriv+=term*(k*(I(8)/3)/r+sum(2/(j-i) for i in range(k)))
    return I('22.152')*(-r*h+j*h.ln()).exp()/r*total, (I(8)/3)*h+2*h.ln()+(I(8)/3)/r+deriv/total

DN=I('.010445')
def QD(L):
    return (DN*L/(L-89)+DN*3*L/((L-92)*(L-89))*(-I('.025')*(L-89)).exp()
        +I('.005')*L**2*(-I('.075')*L).exp()
        +(I('.01')*L**2+118)*(-3*L/8).exp()
        +I('2.091')*L*(-L/8).exp())

def common():
    F=bracket(I('.875'))[0]+8*(h*h+2*h+2)/(3*10**12)
    print('refined density endpoint', F)
    assert F.b<DN.a
    for s,kmax in [('.80',92),('.85',89)]:
        for S,_ in grid(s,'.875','.001'):
            assert bracket(S)[1].b<kmax
    T=(I(40)/8+I('4.65')).exp()
    assert T.a>51 and (I(20).exp()-2-5*T).a>0
    assert I('43.74').exp().b<10**19
    t=I(10**13).ln()
    assert (I('1.25')*2*pi*pi*(-t/2).exp()/t).b<1
    assert (I('2.45')/(2*pi)).ln().b<D('-.9')
    assert ((2+I('.577216')-(4*pi).ln())*(1+I(1)/(4*14**2))).b<D('.0463')
    # H_n - log(n) brackets gamma within 1/n; use the original sharper trapezoid scheme.
    n=1000000; S=10**20; hh=sum(S//j for j in range(1,n+1))
    assert ((I(hh)+n)/S-I(n).ln()-I(1)/(2*n)+I(1)/(n*n)).b<D('.577216')
    # QB's reflected branch is a polynomial with a positive root in (160,190).
    def f(L):return (I(L)/8+I('3.75'))**2-dH*dH+4*pi*I('1.8642')
    assert f(160).b<0 and f(190).a>0
    # Normalized polynomial max by completing the square in 1/L.
    A=1/(256*pi)
    B=I('3.75')/(16*pi)+I('2.091')*(-I('4.65')).exp()
    C=(I('3.75')**2-dH*dH)/(4*pi)+I('1.8642')
    assert C.b<0
    assert (A+B*B/(-4*C)+I('1e-38')).b<D('.001284399')
    assert (-2*C/B).b<1200
    w=I(241); t=w/8+I('3.75')
    assert ((t*t/(2*pi)+I('1.8642'))*(-3*w/8).exp()/w**2).b<D('1e-38')
    print('Common: density slopes, reflected Perron, basic power coefficient verified')

def dnew(L):
    return I(".0463")*(-L/2).exp()+I("3e-12")*(-L/8).exp()+2*(-L).exp()

def chtrial(L):
    out=[]
    for f in ('1','.75','1.25'):
        t=imin(I(3000175332800),imax(I(10**7),I(f)*2*pi*pi*(L/2).exp()/L))
        v=(t/(2*pi)).ln()
        b=pi/(t-1)+pi*pi/(3*t*t)+(v*v/(2*pi)-v/(6*pi))*(-L/2).exp()
        out.append(b)
    return imin(*out)

def err(L,side,mid,mode):
    if side==1 and mid<D('43.74'):return I(0)
    b=imin(chtrial(L),Gas(L))
    if mid>=40:b=imin(b,QB(L)*(-L/8).exp())
    if mode=='density' and mid>=110:b=imin(b,q(L)*(-L/8).exp(),QD(L)*(-L/8).exp())
    cor=-(-L/2).exp() if side==1 else I('1.2551')*((-L/2).exp()+2*L*(-2*L/3).exp())
    return (b+cor)/L+I('.1852')*(-L/2).exp()/L**2+I('12e-12')*(-L/8).exp()/L**2+10000*(-L).exp()

def calibrate(v,a):
    x=I(v); terms=600
    y=sum((x**j-(-1)**j)/(j*factorial(j)) for j in range(1,terms+1))
    tail=2*(x**(terms+1)+1)/((terms+1)*factorial(terms+1))
    F=(x.ln()+y+I(-I(-1).exp().b,tail.b))*(-x).exp()
    assert 2*v<terms and (hp(x,a[:-1])/x).b<F.a and F.b<(hp(x,a)/x).a,(v,F,hp(x,a)/x)

N20,C20=poly(20,4)
N50,C50=poly(50,3)

def loss(L,mid,mode,aa):
    U=hp(L,aa)/L
    A=err(L,1,mid,mode)
    B=err(L-1,-1,mid-1,mode)
    assert A.a>=0 and B.a>=0
    return L**5*B+L**6*A*(2*U+A)

def tailvalue(L,m,mode,aa):
    U=hp(L,aa)/L
    Q=QB if mode=='basic' else QD
    A=(Q(L)+I('1e-8'))*(-L/8).exp()/L
    B=(Q(L-1)+I('1e-8'))*(-(L-1)/8).exp()/(L-1)
    return L**(7+m)*(B/L+A*(2*U+A))

def tailcheck(v,m,mode,aa,cc):
    L=I(v)
    if v<200 or v<=8*(7+m)+1:return False
    if mode=='basic' and (v<241 or (I(m+6)/(L-1)+1/(L-191)).b>=D('.125')):return False
    loss=tailvalue(L,m,mode,aa)
    lower=cc[5+m]-sum(I(-cc[j])/L**(j-m-5) for j in range(m+6,len(cc)) if cc[j]<0)
    return lower.a>loss.b

def gaps(mode):
    calibrate(32,N20)
    calibrate(95,N50)
    for aa,cc,n in [(N20,C20,20),(N50,C50,50)]:
        assert all(k>0 for k in cc[4:n+1])
        assert hp(I(200),aa).b<D('1.04')
    # Both modes use only original non-QRH inputs on this compact strip.
    vals=list(map(D,('0','.11','.20','.42','.50','.71','.75','.90','.92','1')))
    last={v:D('36.4') for v in vals}
    breaks=['36.4','37','39.47','40','41','42','43.74','47.05']
    if mode=='basic':
        for l,u in zip(breaks,breaks[1:]):
            for L,mid in grid(l,u,'.002'):
                e=loss(L,mid,mode,N20)
                low=(hp(L,C20[4:])-e).a
                for v in vals:
                    if low<=v:last[v]=L.b
        print('fixed from end of last uncertified cell through 47.05:',[(str(v),str(last[v])) for v in vals])
        assert last[D(1)]<D('42.5')
    rows=[]
    for m in range(46):
        aa,cc=(N20,C20) if m<=14 else (N50,C50)
        lo=200 if mode=='density' else 241
        hi=3000
        assert tailcheck(hi,m,mode,aa,cc)
        while hi>lo:
            v=(lo+hi)//2
            if tailcheck(v,m,mode,aa,cc):hi=v
            else:lo=v+1
        assert tailcheck(hi,m,mode,aa,cc)
        rows.append(hi)
    print('tail onsets m=0..45:',rows)

def compact(mode):
    calibrate(32,N20)
    W={m:[] for m in range(1,6)}
    breaks=['42','43.74','50','58','59','65','85','110','111','200','201','241','280']
    for l,u in zip(breaks,breaks[1:]):
        step='.025' if D(u)<=85 else '.2'
        for L,mid in grid(l,u,step):
            e=loss(L,mid,mode,N20)
            for m,w in W.items():
                if (hp(L,C20[5+m:])-L**(m+1)*e).a>0:
                    if w and w[-1][1]==L.a:w[-1]=(w[-1][0],L.b)
                    else:w.append((L.a,L.b))
    for m,w in W.items():
        print('compact profile',m,[(str(a),str(b)) for a,b in w if b-a>=D('.5')])

if __name__=='__main__':
    common()
    mode='basic' if '--basic' in sys.argv else 'density'
    gaps(mode)
    compact(mode)

