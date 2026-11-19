from check import I,D,pi,Gas,imin,grid,poly,hp
from repair_check import imax,calibrate,chtrial
from repair_mertens import W3
from math import factorial
import sys
A=(I(1)/8,I(5)/32)
E=(I(7)/8,I(27)/32)
H=3*10**12
h=I(H).ln()
dH=h-(2*pi).ln()
SLOPES=((89,90,91,93,95),(90,91,93,95))
KNOTS=(('.85','.825','.8','.775'),('.825','.8','.775'))
CAP=(I('.010444061'),I('.146294481'))
C1=(I('11.0756'),I('9.7462'))
C2=I('4.1007')

def F(s,c):
    j=5-2*s
    u=1-8*(1-s)/3
    terms=[I(1)]
    for k in range(1,5):
        terms.append(terms[-1]*(j-k+1)/(h*u))
    der=(I(8)/3)*h+2*h.ln()+(I(8)/3)/u+sum(terms[k]*(k*(I(8)/3)/u+sum(2/(j-i) for i in range(k))) for k in range(1,5))/sum(terms)
    return 2*c*(-u*h+j*h.ln()).exp()*sum(terms)/u,der

def constants():
    for i in (0,1):
        f=F(E[i],C1[i])[0]+2*C2*(h*h+2*h+2)/H
        print('edge',i,f)
        assert f.b<CAP[i].a
        knots=[str(E[i].a),*KNOTS[i],'.75']
        for y,z,k in zip(knots[1:],knots,SLOPES[i]):
            vals=[F(S,C1[i])[1].b for S,_ in grid(y,z,'.00025')]
            print('slope',i,y,z,max(vals),k)
            assert max(vals)<k
    for i in (0,1):
        def p(v):
            return (A[i]*I(v)+I('3.75'))**2-dH*dH+4*pi*I('1.8642')
        assert p(0).b<0 and p(190).a>0
    assert (I('2.45')/(2*pi)).ln().b<D('-.9')
    for k in [I(1)/4,*A]:
        for off in ([I(0)] if k.a>D('.2') else [I('4.3'),I('4.4'),I('4.5'),I('4.6'),I('4.65'),I('4.7'),I('6'),I('8')]):
            v=I(110 if off.a==0 else 40)
            t=(k*v+off).exp()
            assert t.a>max(51,v.b) and (v/2).exp().a>5*t.b+2

def densQ(L,i):
    ks=SLOPES[i]
    out=L/(L-ks[0])
    at=I(0); cum=I(0)
    for j,s in enumerate(KNOTS[i]):
        v=E[i]-I(s)
        cum+=ks[j]*(v-at)
        out+=L*(cum-L*v).exp()*(ks[j+1]-ks[j])/((L-ks[j+1])*(L-ks[j]))
        at=v
    return (CAP[i]*out+I('.005')*L**2*(-(I(1)/4-A[i])*L).exp()
          +(I('.01')*L**2+118)*(-(I(1)/2-A[i])*L).exp()
          +I('2.091')*L*(-(I(1)/4-A[i])*L).exp())

def basicQ(L,i,off='4.65'):
    off=I(off)
    t=A[i]*L+off-I('.9')
    return (imax(I(0),(t*t-dH*dH)/(4*pi)+I('1.8642'))
       +(t*t/(2*pi)+I('1.8642'))*(-(I(1)/2-A[i])*L).exp()
       +I('2.091')*(-off).exp()*L)

def perron(L,i):
    return imin(*(basicQ(L,i,k) for k in ['4.65','6','8']))*(-A[i]*L).exp()

def psi(L,i):
    return imin(chtrial(L),Gas(L),perron(L,i),densQ(L,i)*(-A[i]*L).exp(),
        *([I(1)/64*L**2*(-A[i]*L).exp()] if i==1 and L.a>=200 else []))

def d(L,i):
    return I('.0463')*(-L/2).exp()+I('3e-12')*(-A[i]*L).exp()+2*(-L).exp()

def remainder(L,i):
    return I('.1852')*(-L/2).exp()/L**2+I('12e-12')*(-A[i]*L).exp()/L**2+10000*(-L).exp()

def err(L,i,b,side):
    c=-(-L/2).exp() if side==1 else I('1.2551')*((-L/2).exp()+2*L*(-2*L/3).exp())
    return imax(I(0),(b+c)/L+remainder(L,i))

def loss(L,i,n,bf=psi):
    N,C=n
    U=hp(L,N)/L
    aa=err(L,i,bf(L,i),1)
    bb=err(L-1,i,bf(L-1,i),-1)
    return L**5*bb+L**6*aa*(2*U+aa)

def cushion(v,i):
    L=I(v)
    ex=I('1.2551')*((-(I(1)/2-A[i])*L).exp()+2*L*(-(I(2)/3-A[i])*L).exp())
    ex+=I('.1852')*(-(I(1)/2-A[i])*L).exp()/L+I('12e-12')/L+10000*L*(-(1-A[i])*L).exp()
    assert ex.b<D('1e-8')

def tail(v,m,i,n,mode):
    L=I(v); N,C=n
    if v<111 or (I(m+5)/(L-1)).b>=A[i].a:return False
    if mode=='basic':
        if v<200 or (I(m+6)/(L-1)+1/(L-191)).b>=A[i].a:return False
        Q=basicQ
    else: Q=densQ
    aa=(Q(L,i)+I('1e-8'))*(-A[i]*L).exp()/L
    bb=(Q(L-1,i)+I('1e-8'))*(-A[i]*(L-1)).exp()/(L-1)
    u=hp(L,N)/L
    er=L**(m+7)*(bb/L+aa*(2*u+aa))
    j=m+5
    return (C[j]-sum(I(-C[k])/L**(k-j) for k in range(j+1,len(C)) if C[k]<0)).a>er.b

def tails():
    for i in (0,1):
        cushion(110,i)
        def poly_at(n,v,K):
            p=poly(n,K)
            calib_long(v,p[0])
            assert v*(K-1)>=K*(n+2)
            return p
        ns=[(15,poly_at(20,32,4),33),(46,poly_at(50,95,3),96),
          (96,poly_at(100,180,3),181),(156,poly_at(160,275,3),276),
          (206,poly_at(210,360,3),361)]
        for mode in ['density','basic']:
            rows=[]
            for m in range(206):
                n,anchor=next((n,c) for stop,n,c in ns if m<stop)
                assert all(k>0 for k in n[1][4:m+6])
                u=12000;l=max(anchor,111 if mode=='density' else 200)
                assert tail(u,m,i,n,mode)
                while u>l:
                    v=(l+u)//2
                    if tail(v,m,i,n,mode):u=v
                    else:l=v+1
                assert tail(u,m,i,n,mode)
                rows.append(u)
            print('ray',i,mode,'m=0..205',rows,flush=True)

def calib_long(v,aa):
    from check import lo,hi,rn
    saved=[c.prec for c in (lo,hi,rn)]
    for c in (lo,hi,rn): c.prec=300
    x=I(v); terms=4*v
    y=sum((x**j-(-1)**j)/(j*factorial(j)) for j in range(1,terms+1))
    tail=2*(x**(terms+1)+1)/((terms+1)*factorial(terms+1))
    f=(x.ln()+y+I(-I(-1).exp().b,tail.b))*(-x).exp()
    assert (hp(x,aa[:-1])/x).b<f.a and f.b<(hp(x,aa)/x).a,(v,f,hp(x,aa)/x)
    for c,p in zip((lo,hi,rn),saved): c.prec=p

def compact():
    n=poly(50,3); calib_long(95,n[0])
    for i in (0,1):
        starts=['111','125','130','145','155','160','165','170','175','180','185','190','200','201','210','225','250','280','310','340','400']
        windows={m:[] for m in range(1,13)}
        fixed=[]
        for l,u in zip(starts,starts[1:]):
            for L,mid in grid(l,u,'.05'):
                er=loss(L,i,n)
                js=[]
                for m,w in windows.items():
                    if (hp(L,n[1][5+m:])-L**(m+1)*er).a>0:
                        js.append(m)
                        if w and w[-1][1]==L.a:w[-1]=(w[-1][0],L.b)
                        else:w.append((L.a,L.b))
                if L.a==D(l):fixed.append((l,max(js or [0]),str((hp(L,n[1][4:])-er).a)))
        for m,w in windows.items():
            print('compact',i,m,[(str(a),str(b)) for a,b in w if b-a>=D('.25')])
        print('fixed',i,fixed,flush=True)

def mertens():
    from decimal import ROUND_CEILING
    def B(L,i,b):return b+d(L,i)*(1+1/L)+W3(L,False)
    def bound(L,b):return b/(1-b/L)
    def ru(u,k=4):
        return str(u.quantize(D(10)**(u.adjusted()-k+1),rounding=ROUND_CEILING))
    for i in (0,1):
        a=A[i]; v=I(200)
        if i==1:
            off=I('4.65')-I('.9')
            P=a*a/(4*pi)
            P1=a*off/(2*pi)+I('2.091')*(-I('4.65')).exp()
            P0=(off*off-dH*dH)/(4*pi)+I('1.8642')
            assert P0.b<0
            assert P0.b<0
            s=a*v+off
            c=(s*s/(2*pi)+I('1.8642'))*(-(I(1)/2-a)*v).exp()/v**2
            t=(d(v,i)*(1+1/v)+W3(v,False))*(a*v).exp()/v**2
            coef=P-P1*P1/(4*P0)+c+t
            assert (coef/(1-coef*v*(-a*v).exp())).b<D('.0021')
            print('basic .0021 normalized from 200, maximum',coef)
        rows=[]
        for L0 in [111,130,160,170,175,180,190,200,210,220,240,260,300,400,500,750,1000,2000,5000,20000,200000,1000000]:
            L=I(L0)
            v=L/2;y=L/3;j=L/4
            eta=lambda t:I('3.965')/t**2
            power=((-v+a*L).exp()*(1+3*eta(v))+(-2*y+a*L).exp()*(I('.5')+I('2.5')*eta(y))
            +(-3*j+a*L).exp()*(2*(1+eta(j))+(I(1)/3+I(7)/3*eta(j))/(1-(-j).exp())))
            add=(I('.0463')*(-(I(1)/2-a)*L).exp()+I('3e-12')+2*(-(1-a)*L).exp())*(1+1/L)+power
            p=densQ(L,i)+add
            rows.append((L0,ru((p/(1-p*(-a*L).exp()/L)).b,9)))
        print('Mertens density coefficients',i,rows)
        starts=[150,160,165,170,175,180,185,190,195,200,205,210,220,230,240,250,260,280,300,350,400,420]
        L=I(420)
        mx=(bound(L,B(L,i,densQ(L,i)*(-a*L).exp()))*L**2).b
        vals=[(420,ru(mx))]
        for l,r in reversed(list(zip(starts,starts[1:]))):
            for L,_ in grid(l,r,'.125'):
                mx=max(mx,(bound(L,B(L,i,psi(L,i)))*L**2).b)
            vals.append((l,ru(mx)))
        print('Mertens scaled ray',i,vals[::-1],flush=True)
def early_context():
    # Entire closed strip for earlier fixed margins: positive upper sign
    # can be replaced by 0 only through 43.74 in this cell partition.
    from repair_check import err as olderr
    n=poly(20,4); calib_long(32,n[0])
    N,C=n
    def b(L):
        v=L/2-(L/pi).ln()
        t=imin(I(3000175332800),imax(I(10**7),pi*pi*(L/2).exp()/(v-I(1)/6)))
        v=(t/(2*pi)).ln()
        return imin(chtrial(L),Gas(L),pi/(t-1)+pi*pi/(3*t*t)+(v*v/(2*pi)-v/(6*pi))*(-L/2).exp())
    def eval_loss(L,mid):
        U=hp(L,N)/L
        T=L-1
        J=sum((1+k/T+2*(k/T)**2+I('7.59')*(k/T)**3)*(-(1-I(1)/k)*T).exp() for k in (2,3,4))
        J+=I('1.2551')*(2*T-4)*(-4*T/5).exp()
        bb=(b(T)+J)/T+remainder(T,0)
        aa=I(0) if mid<D('43.74') else err(L,0,b(L),1)
        bb=imin(bb,olderr(T,-1,mid-1,'basic'))
        aa=imin(aa,olderr(L,1,mid,'basic'))
        return L**5*bb+L**6*aa*(2*U+aa)
    return C,eval_loss

def extra():
    C,eval_loss=early_context()
    vals=list(map(D,('0','.016','.11','.124','.20','.212','.42','.430','.50','.509','.71','.716','.75','.756','.90','.904','.92','.924','1')))
    last={v:D('36.4') for v in vals}
    breaks=['36.4','39.47','40','41','42','43.74','47.05']
    for l,u in zip(breaks,breaks[1:]):
        for L,mid in grid(l,u,'.002'):
            e=eval_loss(L,mid)
            low=(hp(L,C[4:])-e).a
            for v in vals:
                if low<=v:last[v]=L.b
    print('secondary fixed margins and inclusive ray starts:',[(str(v),str(last[v])) for v in vals])
    for s in ['36.554','36.786','36.988','37.554','37.790','38.520','38.682','39.394','39.504','39.996']:
        L=I(s); print('secondary pointwise at fixed old onset',s,(hp(L,C[4:])-eval_loss(L,D(s))).a)
    assert last[D(1)]<D('39.996')

def early_compact():
    C,eval_loss=early_context()
    W={m:[] for m in (1,2,3,4,5)}
    for l,u in [('42','43.74'),('43.74','60'),('60','75'),('75','95'),('95','125.20')]:
        for L,mid in grid(l,u,'.02'):
            e=eval_loss(L,mid)
            for m,w in W.items():
                if (hp(L,C[5+m:])-L**(m+1)*e).a>0:
                    if w and w[-1][1]==L.a:w[-1]=(w[-1][0],L.b)
                    else:w.append((L.a,L.b))
    for m,w in W.items():print('early secondary profile',m,w)

def strip():
    # For 8000 <= t <= 10000 bound the square boundary via an exact sieve.
    J=10000
    p=[True]*(J+1);p[0]=p[1]=False
    for j in range(2,101):
        if p[j]:
            for k in range(j*j,J+1,j):p[k]=False
    T=I(0); eta0=D(0)
    for n in range(2,J+1):
        if p[n]:T+=I(n).ln()
        if n>=8000:eta0=max(eta0,(1-T/(n+1)).b)
    e0=I('.019')
    print('sieve theta deficit on [8000,10000] at most',eta0)
    assert eta0<e0.a
    S=I(10**19)
    lmin=I(64000000).ln()
    lmax=I(10**13).ln()
    assert Gas(S.ln()).b<D('1e-7')
    assert (3*I('1e-7')*(lmax/2).exp()/S).b<D('1e-10')
    # Ratio W_3*sqrt(x), computed without interval loss from cancellation.
    best=[D(0),D(0)]
    split=I(10000).ln()*2
    for lo,hi,early in [(lmin.a,split.b,True),(split.a,lmax.b,False)]:
        for L,_ in grid(lo,hi,'.01'):
            v=L/2;y=L/3;u=L/4
            assert (I(22)*I(2).ln()).a>v.b
            ev=e0 if early else I('1.751')*(-v/2).exp()+sum((-(1-I(1)/k)*v).exp() for k in range(3,22))
            ev=imin(ev,I('3.965')/v**2,v**2*(-v/2).exp()/(8*pi))
            ey=I('3.965')/y**2
            eu=I('3.965')/u**2
            tiny=I('1e-10')
            wp=1+ev+tiny+(-L/6).exp()*(I('.5')+ey+tiny)+(-L/4).exp()*(2+(I(1)/3+eu+tiny)/(1-(-u).exp()))
            dp=I('.0463')+I('3e-12')*(3*L/8).exp()+2*(-L/2).exp()
            sq_log=1-1/v+2/v**2-6/v**3+24/v**4
            b=I('.791')+dp*(1+1/L)+wp-1+sq_log
            cb=b/(1-b*(-L/2).exp()/L)
            best[0]=max(best[0],(I('.791')+dp+wp).b)
            best[1]=max(best[1],cb.b)
    print('secondary square-root strip weighted and common log coefficients',best)
    for j,C in enumerate(['1.916','1.8292']):assert best[j]<D(C)

def onsets():
    from decimal import ROUND_CEILING
    # Use only analytically monotone upper functions for these inversions.
    def ms(L,i,scale):
        a=A[i]
        p=densQ(L,i)+d(L,i)*(1+1/L)*(a*L).exp()+W3(L,False)*(a*L).exp()
        z=p*(-a*L).exp()/L
        ret=p/(1-z)
        if scale:ret*=L**2*(-a*L).exp()
        return ret
    def invert(pred,l,u):
        assert pred(u)
        while u>l:
            v=(l+u)//2
            if pred(v):u=v
            else:l=v+1
        assert pred(u)
        return str(D(u)/100)
    for i in (0,1):
        vals=['1e-8','1e-9','1e-10','1e-11','1e-12','1e-14','1e-18','1e-24','1e-30']
        print('scaled fixed coefficients/inclusive log onsets',i,[(c,invert(lambda u:ms(I(u)/100,i,True).b<D(c),11100,100000)) for c in vals])
    vals=['.25','.22','.20','.18','.16','.15','.147','.1464','.14630','.146295','.1462945']
    # Below, evaluate normalized exponents directly to avoid Decimal exponent limits.
    def coeff(L):
        a=A[1]; j=L/4; v=L/2;y=L/3
        eta=lambda t:I('3.965')/t**2
        power=((-v+a*L).exp()*(1+3*eta(v))+(-2*y+a*L).exp()*(I('.5')+I('2.5')*eta(y))
            +(-3*j+a*L).exp()*(2*(1+eta(j))+(I(1)/3+I(7)/3*eta(j))/(1-(-j).exp())))
        add=(I('.0463')*(-(I(1)/2-a)*L).exp()+I('3e-12')+2*(-(1-a)*L).exp())*(1+1/L)+power
        p=densQ(L,1)+add
        return p/(1-p*(-a*L).exp()/L)
    # Last row uses a large log; Decimal intervals widened around
    # underflow remain inclusions. No divisions by underflowed terms.
    print('D02 fixed pure-power coefficients/inclusive log onsets',[(c,invert(lambda u:coeff(I(u)/100).b<D(c),11100,200000000000)) for c in vals])
    for i in (0,1):
        offs=['4.65'] if i==0 else ['4.3','4.4','4.5','4.6','4.65','4.7']
        v=I(40)
        a=A[i]
        for offs0 in offs:
            off=I(offs0)-I('.9')
            P=a*a/(4*pi)
            P1=a*off/(2*pi)+I('2.091')*(-I(offs0)).exp()
            P0=(off*off-dH*dH)/(4*pi)+I('1.8642')
            assert P0.b<0
            s=a*v+off
            c=(s*s/(2*pi)+I('1.8642'))*(-(I(1)/2-a)*v).exp()/v**2
            # Bound all cases of the positive part.
            t=(d(v,i)*(1+1/v)+W3(v,False))*(a*v).exp()/v**2
            coef=imax(P-P1*P1/(4*P0),I('2.091')*(-I(offs0)).exp()/v)+c+t
            print('basic maximum on L>=40',i,offs0,(coef/(1-coef*v*(-a*v).exp())).b)
    for i in (0,1):
        a=A[i]
        off=I('3.75')
        P1=a*off/(2*pi)+I('2.091')*(-I('4.65')).exp()
        P0=(off*off-dH*dH)/(4*pi)+I('1.8642')
        assert (-2*P0/P1).b<1200
        for v in (200,500,1200,5000):
            L=I(v)
            u=(basicQ(L,i)*(-a*L).exp()+d(L,i)*(1+1/L)+W3(L,False))*(a*L).exp()/L**2
            print('basic normalized at',i,v,(u/(1-u*L*(-a*L).exp())).b)

def smoothed(L,i):
    return I('2.451e-6')*(-A[i]*L/2).exp()

def smoothcheck():
    for i in (0,1):
        L=I(110); a=A[i]; c=I('2.45e-6')
        delta=c*(-a*L/2).exp()
        assert delta.b<D('1e-8')
        # d* upgraded: .046301 all beta <= half and 1.5e-12 remaining.
        k=(1+(1+I('1e-8'))**2)
        val=c/2+k/c*(I('.046301')*(-(I(1)/2-a)*L).exp()+I('1.5e-12')+2*(-(1-a)*L).exp())
        assert val.b<D('2.451e-6')
        print('smoothed proof bracket',i,val)
    def bb(L,i):return imin(chtrial(L),Gas(L),perron(L,i),smoothed(L,i))
    n=poly(50,3); calib_long(95,n[0])
    def lower(L,m,i):
        N,C=n
        er=loss(L,i,n,bb)
        return hp(L,C[5+m:])-L**(m+1)*er
    for i in (0,1):
        W={m:[] for m in (1,2,3,4)}
        for L,_ in grid(185,310,'.025'):
            for m,w in W.items():
                if lower(L,m,i).a>0:
                    if w and w[-1][1]==L.a:w[-1]=(w[-1][0],L.b)
                    else:w.append((L.a,L.b))
        for m,w in W.items():print('smoothed table-free compact',i,m,w)

def dens_sq(L,i):
    # Reciprocal-square analog of the high-density main term.
    k=SLOPES[i]
    q=L/(L-k[0]); v0=I(0); f=I(0)
    for j,s in enumerate(KNOTS[i]):
        v=E[i]-I(s); f+=k[j]*(v-v0)
        q+=L*(f-L*v).exp()*(k[j+1]-k[j])/((L-k[j+1])*(L-k[j]))
        v0=v
    return I('2.504947e-15' if i==0 else '3.1525781e-14')*q
def q2check():
    def F2(s,c):
        j=5-2*s
        u=2-8*(1-s)/3
        terms=[I(1)]
        for k in range(1,5):terms.append(terms[-1]*(j-k+1)/(h*u))
        der=(I(8)/3)*h+2*h.ln()+(I(8)/3)/u+sum(terms[k]*(k*(I(8)/3)/u+sum(2/(j-i) for i in range(k))) for k in range(1,5))/sum(terms)
        return 4*c*(-u*h+j*h.ln()).exp()*sum(terms)/u,der
    for i in (0,1):
        ep=F2(E[i],C1[i])[0]+4*C2*(h*h/2+h/2+I(1)/4)/H**2
        print('reciprocal-square density edge',i,ep)
        assert ep.b<D('2.504947e-15' if i==0 else '3.1525781e-14')
        knots=[str(E[i].a),*KNOTS[i],'.75']
        for y,z,k in zip(knots[1:],knots,SLOPES[i]):
            assert all(F2(S,C1[i])[1].b<k for S,_ in grid(y,z,'.00025'))
    for i in (0,1):
        assert spectral_square(I('110.9999999'),i).b<D('2.5e-17')
        for v in [150,155,160,164,166,168,170,172,175,180,190,200]:
            L=I(v)
            d=spectral_square(L-I('1e-7'),i)
            s=I('2.000001')*(d.ln()/2).exp()
            print('advanced smooth trial',i,v,str(s.b),str(psi(L,i).b),s.b<psi(L,i).a)
def spectral_square(L,i):
    return (I('.046301')*(-L/2).exp()+I('1.5e-12')*(-L/4).exp()+dens_sq(L,i)*(-A[i]*L).exp()+2*(-L).exp())

def basic_mid():
    from decimal import ROUND_CEILING
    for i in (0,1):
        a=A[i]; C=I('.001285' if i==0 else '.0020012')
        L=I(420)
        mx=(C*L**4*(-a*L).exp()).b
        v=[150,165,175,180,185,190,195,200,205,210,220,230,240,250,260,280,300,350,400,420]
        res=[(420,mx)]
        for b,e in reversed(list(zip(v,v[1:]))):
            for L,_ in grid(b,e,'.125'):
                m=imin(perron(L,i),Gas(L),chtrial(L),smoothed(L,i))
                B=m+d(L,i)*(1+1/L)+W3(L,False)
                assert (B/L).b<1
                mx=max(mx,(B*L**2/(1-B/L)).b)
            res.append((b,mx))
        print('basic matched Mertens scaled rays',i,[(t,str(x.quantize(D(10)**(x.adjusted()-3),rounding=ROUND_CEILING))) for t,x in res[::-1]])

def centered():
    v=I(200)
    assert hp(v,poly(20,4)[0]).b<D('1.01')
    for i, cap, hi in [(0,'.019','.061'),(1,'.267','.86')]:
        C=I(cap)
        assert (densQ(v,i)+I('1e-8')).b<C.a
        assert (C*(-A[i]*v).exp()).b<D('.001')
        k=(I(201)/200*A[i].exp()+I('2.021'))*C
        assert k.b<D(hi)
        print('centered uniform gap constant',i,k)

if __name__=='__main__':
    for arg in sys.argv[1:]:
        globals()[arg]()
