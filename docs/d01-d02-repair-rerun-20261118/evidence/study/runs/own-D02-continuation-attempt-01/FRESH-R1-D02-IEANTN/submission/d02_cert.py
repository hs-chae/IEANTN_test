"""Outward certificates for D02; run with /usr/bin/python3.10."""
from verify import I,D,pi,fac,comb,H,c,dense
from functools import lru_cache
E=lambda x:I(x).exp()
F=lambda x:I(str(x))
CAP0=D(".875")
CAP2=D(".84375")
R0=D(".125")
R2=D(".15625")
SIG=(D(".75"),D(".77"),D(".78"),D(".79"),D(".80"),D(".81"),D(".82"))
RT=(D(".20"),D(".225"),D(".25"),D(".275"),D(".30"))
def lt(x,y):
    assert I(x).b<I(y).a,(x,y)
BINS=[
 ("7.8","4.101"),("8.162","3.693"),("8.538","3.613"),
 ("8.927","3.533"),("9.330","3.453"),("9.747","3.373"),
 ("10.176","3.293"),("10.620","3.213"),("11.076","3.133")]
h=I(H).log()
@lru_cache(None)
def W(s,j):
    a,b=map(I,BINS[j])
    r=(8*I(s)-5)/3; q=5-2*I(s)
    f=I(1); Q=f
    for k in range(1,5):
        f*=q-(k-1)
        Q+=f/(r*h)**k
    return a*E(-r*h)*h**q/r*Q+b*(h*h+2*h+2)/H
KNOTS=[D(x) for x in (".75",".76",".77",".78",".79",".795",".80",".805",".81",
           ".815",".82",".825",".83",".835",".84",".84375",".85",".855",
           ".86",".865",".87",".875")]
def index(s):return max(0,int(s*100)-79)
def max_i(a,b):return I(max(a.a,b.a),max(a.b,b.b))
def knot(s):
    j=index(s)
    return max_i(W(s,j),W(s,j-1)) if j>0 and s*100==int(s*100) else W(s,j)
@lru_cache(None)
def mixture(cap,s0):
    cs=[s for s in KNOTS if s0<=s<=cap]
    assert cs[0]==s0 and cs[-1]==cap
    ws=[knot(s) for s in cs]
    lis=[(a,b,w,(w/v).log()/(b-a)) for a,b,w,v in zip(cs,cs[1:],ws,ws[1:])]
    assert all(r.a>0 for _,_,_,r in lis)
    return ws[-1],lis
def erel(x):
    if x.a<=0<=x.b: return I(E(x.a).a,E(x.b).b)
    return (E(x)-1)/x
@lru_cache(None)
def terms(cap,s0,k):
    if s0 is None: return [(1-cap,I(".0142"),2),(D(".25"),I("2.091"),1)]
    if s0=="raw": return [(1-cap,1/I(64),2)]
    a=I(k)**2/(4*pi)+I(".9321")/100**2
    return [(1-s0,a,2),(D(".5"),2*a,2),(k,I("2.091"),1)]
def evalterms(L,tr,scale=0):
    return sum(a*L**p*E((I(scale)-r)*L) for r,a,p in tr)
def local(L,cap,s0,k,scale=0):
    L=I(L)
    assert L.a>=100
    if s0 is None or s0=="raw":
        assert L.a>=(200 if s0=="raw" else 100)
        return evalterms(L,terms(cap,s0,k),scale)
    w,ls=mixture(cap,s0)
    z=I(scale)
    return (evalterms(L,terms(cap,s0,k),scale)+2*w*E((z+cap-1)*L)
        +2*sum(q*w*(b-a)*E((z+a-1)*L)*erel((L-q)*(b-a)) for a,b,w,q in ls))
def slow(cap):
    return 1-cap
def J(L,cap):
    L=I(L)
    return I(".0462")*E(-L/2)+I("4e-12")*E(-I(slow(cap))*L)+2*E(-L)
def Wpi(L,cap):
    L=I(L); r=I(slow(cap))
    return (3*E(7)+2)*L*E(-L)+(I(".0462")*(1+(1+I(14)/3)/14)*E(-L/2)+I("4e-12")*(1+(1+1/(1-r-I(2)/7))/14)*E(-r*L)+4*E(-L))/L
def Vpi(L):
    L=I(L)
    return I("1.000000147")*E(-L/2)*(1+I(14)/(3*L))+I("1.78")*E(-2*L/3)*(1+21/L)
d=c+114*E("-14.5")
def V(L):
    L=I(L)
    return (1+7*E(-L/4)+3*d)*E(-L/2)+I("3.8")*E(-2*L/3)
def mW(L,cap,s0,k,scale):
    L=I(L); r=I(slow(cap)); z=I(scale)
    return local(L,cap,s0,k,scale)+(1+1/L)*(I(".0462")*E((z-I(".5"))*L)+
      I("4e-12")*E((z-r)*L)+2*E((z-1)*L))+(1+7*E(-L/4)+3*d)*E((z-I(".5"))*L)+I("3.8")*E((z-I(2)/3)*L)
def mcoef(L,cap,s0,k,scale):
    L=I(L)
    U=mW(L,cap,s0,k,scale)
    return U*E(U*E(-I(scale)*L)/L)
def elementary():
    for k in RT:
        t=I(100)
        assert I(k).a>=(1/t).b
        lt(100,E(t*k)); lt(51,E(t*k))
        lt(5*E((I(k)-I(".5"))*t)+2*E(-t/2),1)
    lt(I("2.45"),2*pi)
    lt((I(".0462")*E(I(7)/2)/49+I("4e-12")*E(7*CAP0)/49)*(1+1/I(14))+4*I(1)/49+I(2)/7,2)
    lt(I(".0142")+I("2.091")/200*E(-I(200)*(I(".25")-R2)),1/I(64))
    for cap in [CAP0,CAP2]:
        for s in SIG:
            for k in RT:
                mixture(cap,s)
                for r,a,p in terms(cap,s,k):
                    assert a.a>0 and r>=slow(cap)
                    lt(I(p)/100,r) # unscaled monotonicity
def mdecreasing(a,cap,s0,k,z):
    # On the whole ray all monomials making up exp(zL)*W decrease.
    for r,_,p in terms(cap,s0,k):
        assert I(p).b<=((I(r)-z)*I(a)).a or (p==0 and r==z)
def fcoeff(m,j):
    return (sum(fac(i)*comb(j,i) for i in range(min(j,m)+1))
         -sum(fac(i)*fac(j-i) for i in range(max(0,j-m),min(j,m)+1)))
@lru_cache(None)
def coeffs(m):
    return [fcoeff(m,j) for j in range(2*m+1)]
def S(m,L):return sum(fac(j)/L**j for j in range(m+1))
def remainder(m,L):
    b=2*(m+2)
    return 3*L*E(b-L)+2*fac(m+1)/L**(m+1)
def em(L,m,cap,s0,k):
    if s0=="raw":
        assert L.a>=200 and cap==CAP2
        r=I(R2)
        return (I("4e-17")*L*E(200-L)+local(L,cap,s0,k)*(1+1/((1-r)*L))+
                  3*E(-L/2)*(1+1/(I(".48")*L))+remainder(m,L))
    return local(L,cap,s0,k)+Wpi(L,cap)+Vpi(L)+remainder(m,L)
def compare(n,a,m,cap,s0,k,eta=0,cert=True):
    # Proves Y>P_n + eta*C_(n+1)/L^(n-3).
    L=I(a); z=L-1; C=coeffs(m); eta=I(eta)
    w,v=em(L,m,cap,s0,k),em(z,m,cap,s0,k)
    loss=L**(m-1)*(L/z*v+2*S(m,L)*w+w*w)
    rhs=sum(C[j]*L**(m-1-j) for j in range(n+1,m))-eta*C[n+1]*L**(m-n-2)
    if cert:
        assert m>=n+2 and z.a>=max(100,2*(m+2))
        assert 0<=eta.a<=eta.b<1
        assert C[:4]==[0]*4 and min(C[4:m+1])>0
        lt(sum(max(0,-C[j])/L**(j-m) for j in range(m+1,2*m+1)),C[m])
        for r,_,p in terms(cap,s0,k)+[(slow(cap),None,0),(D(".5"),None,0),(D(1),None,1)]:
            lt(I(m-1+p)/z,r)
        lt(loss,rhs)
        print("factorial",cap,n,a,m,s0,k,eta.a,"ratio<", (loss/rhs).b,flush=True)
    return (loss/rhs).b

def Useven(L):return I(".9999")*E(-L/2)*(1+2/L*(1-E((7-L)/2)))
def ch2(L,shift):
    T=2*pi*pi*E(L/2)/(L-I(shift))
    assert T.a>10**7 and T.b<=H and E(L).a>max(T.b,10**9)
    y=pi/T; h=(T/(2*pi)).log()
    f=(h*h/(2*pi)-h/(6*pi))*E(-L/2)+pi/(T-1)
    return -f,f+y*y/2  # 1<=y coth y<=1+y²/2 via CH2 Lemma 4.2
def errside(L,cap,up,k=D(".25"),s0=D(".75")):
    from verify import E as oldE
    # Error from Li2 for new branches. In oldE the extra Li2 remainder is included.
    M=[(c+I("113.67")*E(-L/2),)*2]
    if L.a>=34 and L.b<=58:
        w=2*(L/(pi*E(1))).log()
        f=((L-w)**2-4)*E(-L/2)/(8*pi)
        M.append((f,f))
        for sh in (0,3,4,5):
            Tp=2*pi*pi*E(L/2)/(L-sh)
            if Tp.a>10**7 and Tp.b<H and E(L).a>max(Tp.b,10**9):
                l,h=ch2(L,sh)
                M.append((-l,h))
    if L.a>=160:
        f=local(L,cap,s0,k); M.append((f,f))
    mag=min(p[int(up)].b for p in M)
    bound=I(mag)+Wpi(L,cap)+(-Useven(L) if up else Vpi(L))
    if up: bound+=13*L*E(-L)+3*fac(19)/L**19
    return I(max(0,min(bound.b,oldE(L,True,up).b)))
def finitegap(L,cap,pv=False,n=0):
    from verify import g, C, part
    u,v=errside(L,cap,True),errside(L-1,cap,False)
    if pv:
        assert E(L).b<I("1.2e17").a
        u=I(min(u.b,(16*L*E(-L)+3*fac(19)/L**19).b))
    if n:
        assert 4<=n<=17
        # The same absorption check as in verify.py keeps all coefficients <=26
        # and absorbs the negatives using C27.
        base=sum(C[j]/I(L.b)**(j-4) for j in range(n+1,27))
    else: base=g(L.b)
    return base-L**4*(L/(L-1)*v+2*S(18,L)*u+u*u)
def cells(a,b,q,cap,pv=False,n=0):
    stack=[(D(a),D(b))]
    out=D("Infinity");cnt=0
    while stack:
        x,y=stack.pop()
        box=I(x,y)
        z=finitegap(box,cap,pv,n)-I(q)
        if z.a>0:
            out=min(out,z.a);cnt+=1
        elif y-x>D("1e-7"):
            mid=(x+y)/2
            stack.extend([(mid,y),(x,mid)])
        else: raise ArithmeticError((x,y,z))
    print("closed cells",cap,a,b,q,pv,n,cnt,"excess>",out,flush=True)
def Vplus(L):
    L=I(L)
    B=I("2.415001")
    N=E(29)
    return sum((1/I(j-1)+B*E(-L/(2*j))+I("1.78")*E(-2*L/(3*j)))*E(-(j-1)*L/j)
        +j*c/(j-1)*N**(1-j)+j*I("113.67")/(I(j)-I(".5"))*E((I(".5")-j)*29) for j in [2,3])+I("3.46")*E(-3*L/4)
def earlyW(L,cap):
    L=I(L)
    return I(".791")*E(-L/2)+(1+1/L)*J(L,cap)+Vplus(L)

def gamma(n=100000):
    t=sum(I(1)/i for i in range(1,n+1))-I(n).log()-I(1)/(2*n)
    return t+I((1/I(12*(n+1)**2)).a,(1/I(12*(n-1)**2)).b)

def econst():
    N=E(29)
    return sum(j*c/(j-1)*N**(1-j)+j*I("113.67")/(I(j)-I(".5"))*E((I(".5")-j)*29) for j in [2,3])
def earlytest(a,z=0,poly=False,cap=CAP0):
    a=I(a)
    z=I(z)
    w=earlyW(a,cap)
    w0=w-econst()
    # All nonconstant terms decrease after scaling; constants grow toward 29.
    cof=(w0*E(z*a)*a**(2*poly)+econst()*E(z*29)*29**(2*poly))
    return cof*E(w/a)
def midtest(a,b,cap,z=0,poly=False):
    a,b,z=I(a),I(b),I(z)
    r=I(slow(cap))
    w0=c+115*E(-a/2)+I("4.1e-12")*E(-r*a)
    return (c*E(z*b)*b**(2*poly)+a**(2*poly)*(115*E((z-I(".5"))*a)+
               I("4.1e-12")*E((z-r)*a)))*E(w0/a)
def band29(z=0,poly=False):
    z=I(z);L=I(29)
    w=(L**2/(8*pi)+I("1.25"))*E(-L/2)
    return I("1.0001")*w*E(z*L)*L**(2*poly)
def power(a,b,cap,z,K=None,s=D(".75"),k=D(".275")):
    a,b,z=D(a),D(b),D(z)
    assert 10<=a<=b and b>=100 and 0<=z<=slow(cap)
    val=[]
    if a<=29: val.append(earlytest(a,z,False,cap))
    if a<=58: val.append(band29(z,False))
    if a<=b: val.append(midtest(max(a,58),b,cap,z))
    mdecreasing(b,cap,s,k,z)
    val.append(mcoef(b,cap,s,k,z))
    high=max(x.b for x in val)
    if K is not None:
        lt(high,K)
        print("power join cap, scale, a,b,K",cap,z,a,b,K,"upper",high,flush=True)
    return high
def mverify_common():
    lt(E(29),10**13)
    lt(121,E(5))
    from early import primes
    theta=I(0)
    for p in primes(121):
        theta+=I(p).log()
        lt(theta,p)
    lt(1+c+I("113.67")*E("-14.5"),"1.000058")
    lt(I("1.000058")*(2+I(4)/3/(1-E(-I(10)/4))),"3.46")
    lt(10**4,E(10))
    # The low RH zero sum identity gives a smaller coefficient, used everywhere in J.
    gamma_upper=sum(I(1)/j for j in range(1,1001))-I(1000).log()-I(1)/2000+I(1)/10**6
    lt(2+gamma_upper-(4*pi).log(),".0462")
    lt(I("113.67")+(1+7*E(-I(58)/4)+3*d)+I("3.8")*E(-I(58)/6)+
       (1+I(1)/58)*(I(".0462")+2*E(-29)),115)
    lt((1+I(1)/58)*I("4e-12"),"4.1e-12")
    for a,K in [(17,".117"),("17.3",".104"),(18,".079"),("18.8",".057"),("19.25",".047"),("19.5",".043")]:
        lt(earlytest(a,poly=True),K)
        lt(band29(poly=True),K)
        lt(midtest(58,230,CAP0,poly=True),K)
        base=I(230)
        free=I(".0142")*base**2*E(-base/8)+I("2.091")*base*E(-base/4)+(1+1/base)*J(base,CAP0)+V(base)
        lt(free*E(free/base)*base**2,K)
        print("new original-only polynomial tail",a,K,flush=True)
