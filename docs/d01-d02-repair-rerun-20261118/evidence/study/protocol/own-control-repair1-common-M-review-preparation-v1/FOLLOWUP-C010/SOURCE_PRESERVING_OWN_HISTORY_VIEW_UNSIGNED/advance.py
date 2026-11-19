#!/usr/bin/python3.10
from bounds import *

def a(j): return (I(1) if j==0 else I('1.25'))/8
@lru_cache(maxsize=8192)
def d_light(x,j):
    L=I(x); Y=a(j)*L+L.ln()
    return (Q('3.491')+Q('.17')*(Y+1)*(Y+2))*(-a(j)*L).exp()

def d_split(x,j):
    L=I(x); Y=a(j)*L+L.ln()
    v=Y+I('2.45').ln()
    diff=v-h
    W=I(max(Q(0),diff.l),max(Q(0),diff.r))
    c=1/(2*PI)+(Q('.137')*h+Q('.443'))/(H*h*(h-(2*PI).ln()))
    rr=Q('.137')*h+Q('.443')*h.ln()+Q('1.588')
    return (Q('2.091')+2*(c*W*((v+h)/2-(2*PI).ln())+2*rr/H))*(-a(j)*L).exp()+        (Q('1.4')+Q('.17')*(h+1)*(h+2))*(-L/2).exp()

# Quarter original bin width, positive increments with the same source constants.
def new_table():
    bs=[]; ri=0
    for r in range(9600,11200):
        while ri+1<len(rows) and rows[ri+1][0]*4<=r:ri+=1
        _,c,d=rows[ri]
        s=I(r)/12800
        aa=(8*s-5)/3;q=5-2*s
        sm=term=I(1)
        for k in range(1,5):
            term*=(q-k+1)/(aa*h);sm+=term
        val=2*(I(c)*(q*h.ln()-aa*h).exp()/aa*sm+I(d)*(h*h+2*h+2)/H)
        bs.append(min(val.r,bs[-1]) if bs else val.r)
    return bs
BS4=new_table()

@lru_cache(maxsize=8192)
def d_fine(x,j):
    L=I(x); end=1200 if j else 1600
    w=(-L/12800).exp(); pw=w**(3200-end)
    # Sum positive coefficients, Horner from the lower end.
    v=I(0)
    for i in range(end-1):
        v=v*w+(I(BS4[i])-BS4[i+1])
    v=v*w+BS4[end-1]
    return v*pw+Q('2.091')*L*(-L/3).exp()+L**2/16*(-L/4).exp()

def primeB(L,j,f):
    d=f(L,j);l=I(L)
    return d*(1+Q('2.23' if f is d_split else '1.63')/l)+Q('1.000001')*(1+Q('2.23')/l)*(-l/2).exp()+Q('1.78')*(1+Q('3.53')/l)*(-2*l/3).exp()+40000000*l*(-l).exp()

def signed_part(x,j,early,f):
    L=I(x);aa=a(j)
    J=(Q('.1645')*(-L/2).exp()+Q('8e-12')*(1+1/(Q('.9')-aa))*(-aa*L).exp()
        +Q('1.838')*(-L).exp()+(-3*L).exp())/L+3104*L*(-L).exp()
    p=A_C(L)
    if early and x>=34:
        p=imin(p,((L-2*(L/(PI*E)).ln())**2-4)/(8*PI)*(-L/2).exp())
    if x>=40:p=imin(p,f(x,j))
    drift=(Q('1.000001')*(1+Q('2.5')/L)*(-L/2).exp()
           +Q('1.78')*(1+I(30)/7/L)*(-2*L/3).exp())
    return p+J,p+J+drift

def errors(l,r,j,f,signed):
    def simp(t,early):
        p=bC(t)
        if early:p=imin(p,bF(t))
        if t>=40:p=imin(p,primeB(t,j,f))
        return upper(p)
    lv=F.subtract(l,Q(1))
    bu,bw=simp(l,r<=58),simp(lv,r<=59)
    if not signed:return bu,bw
    pu,_=signed_part(l,j,r<=58,f)
    _,pw=signed_part(lv,j,r<=59,f)
    return I(0,max(Q(0),imin(bu,pu-Q('.9999')*(-I(r)/2).exp()).r)),upper(imin(bw,pw))

def ram_row(k,m,u,j,f,signed):
    m,u=Q(m),Q(u); d=k+(m==cs[k]); T=Q(450 if k<=8 else 650); t=I(T)
    assert d+6 < (T-1)/8 and d+4 < 21
    assertlt(loss(t,t,primeB(T,j,f),primeB(T-1,j,f),d)+sum(-c/t**(i-d) for i,c in enumerate(cs) if c<0),
             cs[d]-(0 if d>k else m))
    def part(l,r):
        p,q=I(l),I(r)
        ub,wb=errors(l,r,j,f,signed)
        if (resmain(p,q,k)-loss(p,q,ub,wb,k)).l>m:return 1
        assert r-l>Q('.000001'),(l,r,k,j,m,resmain(p,q,k)-loss(p,q,ub,wb,k))
        mid=N.divide(N.add(l,r),Q(2))
        return part(l,mid)+part(mid,r)
    ends=[u]+[Q(t) for t in [34,35,40,41,58,59,80,125,166,169,189,190,230,300,375] if u<t<T]+[T]
    return sum(part(l,r) for l,r in zip(ends,ends[1:]))

def point(k,u,j,f,signed):
    u=Q(u); l=I(u); e1,e2=errors(u,u,j,f,signed)
    return resmain(l,l,k)-loss(l,l,e1,e2,k)
def mert_point(u,j,f):
    l=I(u);v,w=mux(l,j,f(l.l,j),'1.34')
    assert 0<=w.l<=w.r<1
    return l*w/(1-w)

def split_m_ray(j):
    L=I(300); aa=a(j)
    v=aa*L+L.ln()+I('2.45').ln()
    log2pi=(2*PI).ln()
    assertlt(0,v-h)
    assertlt(0,v+h-2*log2pi)
    assertlt((aa+1/L)*(1/(v-h)+1/(v+h-2*log2pi)),aa)
    assertlt(1,L.ln()+I('2.45').ln()-log2pi)
    c=1/(2*PI)+(Q('.137')*h+Q('.443'))/(H*h*(h-log2pi))
    neg=c*(h-log2pi)**2
    target=Q('.00408' if j else '.00262')
    for l in range(300,2501,5):
        L=I(l); r=l+5
        _,w=mux(L,j,d_split(l,j),'1.34')
        assert 0<=w.l<=w.r<1
        # The last check drops the entire negative term for the analytic tail.
        ans=(L*w*(aa*L).exp()/L**2+neg/L**2-(0 if l==2500 else neg/I(r)**2))/(1-w)
        assertlt(ans,target)
    print('split M whole-ray',j,300,target,440,ans,flush=True)

def early_sign():
    L=I('15.4')
    assertlt(10**4,L.exp())
    assertlt(I(10**13).ln(),30)
    assertlt(Q('.047')+Q('8e-12')*(I(30)*3/8).exp()+
             Q('1.838')*(-L/2).exp()+(-5*L/2).exp(),Q('.048'))
    for u,c in [('15.4','.0012'),('18','.0556')]:
        L=I(u)
        cf=1-5*I('3.965')*9/L**2
        assertlt(0,cf)
        low=1-3*I('3.965')*4/L**2-Q('.751')-Q('.048')+cf*(-I(30)/6).exp()/2
        assertlt(Q(c),low)
        print('signed weighted',u,c,low,flush=True)
    assertlt(32321,(I('20.77')/2).exp())
    for u,c in [('20.6','.00015'),('20.77','.0889')]:
        L=I(u)
        delta=I('3.965')*4/L**2 if u=='20.6' else 80/L**3
        main=1-2/L+8/L**2-48/L**3
        assertlt(8,L/2) # keeps the derivative of main positive
        cf=1-I(3)/(2*L)-I('3.965')*9/L**2*(5+3/L)
        assertlt(0,cf)
        low=main-delta*(3+2/L)-Q('.751')-(1+1/L)*Q('.048')-L*(-L/2).exp()+cf*(-I(30)/6).exp()/2
        assertlt(Q(c),low)
        print('signed reciprocal/log',u,c,low,flush=True)

if __name__=='__main__':
    if 'certify' in sys.argv:
        early_sign()
        for j in (0,1):
            u=I(40); T=u*(a(j)*u).exp()
            assertlt(51,T);assertlt(5*T+2,(u/2).exp())
            assertlt(u,T)
            assertlt(a(j)+1/u,I(1)/2)
            # Split endpoint decrease from both smallest used shifted arguments.
            l=I(238 if j else 315)
            def loggain(l):
                v=a(j)*l+l.ln()+I('2.45').ln()
                assertlt(0,v-h);assertlt(0,v+h-2*(2*PI).ln())
                return (a(j)+1/l)*(1/(v-h)+1/(v+h-2*(2*PI).ln()))
            assertlt(loggain(l),a(j))
            assertlt(loggain(I(449))+I(14)/449,a(j))
            L=I(300)
            c=[Q('.003814'),Q('.005563')][j]
            assertlt(mert_point(300,j,d_light)*(a(j)*L).exp()/L**2,c)
            print('density-free M',j,300,c,flush=True)
            split_m_ray(j)
        assertlt(Q('.005563')*(-I(300)/32).exp(),Q('.003814'))
        assertlt(Q('.00408')*(-I(300)/32).exp(),Q('.00262'))
        assertlt(Q('.0104'),I(BS4[-1]))
        for L,c0,c1 in [(170,'.020787','.292652'),(200,'.018115','.254039'),
                        (250,'.015824','.221409'),(300,'.014599','.204091'),
                        (1000,'.011489','.160892')]:
            for j,c in enumerate([c0,c1]):
                zz=mert_point(L,j,d_fine)*(a(j)*I(L)).exp()
                assertlt(zz,Q(c))
            assertlt(Q(c1)*(-I(L)/32).exp(),Q(c0))
            print('finer M',L,c0,c1,flush=True)
        L=I('168.745')
        z=mert_point(L.l,1,d_fine)
        p=signed_part(L.l,1,False,d_fine)[0]
        for q in (I('1.045e-12'),Q('.01')*(-L/8).exp()):
            assertlt(z,q);assertlt(p,q)
        for q in (I('1e-15'),Q('.0004')*(-L/8).exp()):
            assertlt(3*(-L/2).exp(),q)
        print('strict floors checked at',L,flush=True)
        L=I(342); v=a(1)*L+L.ln()+I('2.45').ln()
        assertlt(0,v-h);assertlt(0,v+h-2*(2*PI).ln())
        assertlt((a(1)+1/L)*(1/(v-h)+1/(v+h-2*(2*PI).ln())),I(1)/32)
        for q in (I('1.045e-12'),Q('.01')*(-L/8).exp()):
            assertlt(mert_point(L.l,1,d_split),q)
            assertlt(signed_part(L.l,1,False,d_split)[0],q)
        print('density-free strict comparison anchors',L,flush=True)
        L=I('168.745')
        # Smooth Xi comparisons with all retained direct pi uppers.
        assertlt(sum(I(factorial(k))/L**(k-3) for k in range(3,21))+L**3*err(L),Q('6.3'))
        assertlt(Q('7.32')/L**3,Q('.53816')/L**2)
        assertlt(1/L+2/L**2+Q('7.32')/L**3,Q('.2551'))
        assertlt(2/L+Q('7.32')/L**2,Q('.112'))
        assertlt(Q('7.32')/L,Q('.2311'))
        assertlt(I('1e-12')+I('4.6e-14'),1/I(190)**3)
        assertlt(Q('.0104')*(-I(190)/8).exp(),1/I(190)**3)
        t=I(2000)
        sqrt=lambda v:(v.ln()/2).exp()
        pt=235*(Q('1.52')*t.ln()-Q('.8')*sqrt(t)).exp()
        assertlt(2*(2/LN2)*t*(-t).exp(),pt)
        assertlt(Q('.0104')*(-t/8).exp(),pt/2)
        t=I(3914)
        assertlt(Q('.19')+Q('.002'),720*(1/t+196/t**2))
        assertlt(Q('.0104')*(-t/8).exp(),Q('.002')/t**5)
        print('direct pi upper comparison anchors OK',flush=True)
        for f,k,m,x,y in [(d_fine,2,'80.9','196.58','48.95'),
                          (d_fine,3,'1412','253.55','211.04'),
                          (d_split,2,'145','316','239'),
                          (d_split,3,'1412','353','268')]:
            for j,L in enumerate([x,y]):
                print('new Ram',f.__name__,k,m,j,L,ram_row(k,m,L,j,f,True),flush=True)
        for k,x,y in [(6,'358.1','288.8'),(7,'394','315.2'),(8,'430','342'),
                      (9,'466','369'),(10,'502','396'),(11,'538','424'),
                      (12,'575','450')]:
            for j,L in enumerate([x,y]):
                print('deep Ram',k,cs[k],j,L,ram_row(k,cs[k],L,j,d_fine,True),flush=True)
    if 'explore' in sys.argv:
        for k,f,us in [(2,d_fine,[49,165,166,167,168,169,190,195,196,197]),
                       (3,d_fine,[210,211,252,253]),
                       (2,d_light,[245,250,255,260,265,270,275,290,300,320,330,340]),
                       (3,d_light,[290,300,310,315,320,350,360,370,380,390])]:
            for L in us:
                print('sample',f.__name__,k,L,[float(point(k,L,j,f,True).l) for j in (0,1)])
        for L in [168,168.5,168.6,168.7,168.8,170,175,180,200,250,300,1000]:
            print('sample M',L,[float(mert_point(L,j,d_fine).r*(a(j)*I(L)).exp().r) for j in (0,1)],
                  float(mert_point(L,1,d_fine).r))
        for j in (0,1):
            L=I(300)
            print('sample light',j,float((mert_point(300,j,d_light)*(a(j)*L).exp()/L**2).r))
