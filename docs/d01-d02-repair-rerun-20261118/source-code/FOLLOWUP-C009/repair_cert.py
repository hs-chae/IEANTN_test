"""Exact certificates for the post-review B0-only additions."""
from cert import I,F,S,exp,ln,f,comb,co,U,a,qr,PI
from mcert import W,rows,zc,dc
from functools import lru_cache

H=3000175332800
h=ln(H)
K=I('.010443624')
b=F(7,8)
kap=F(2,5)
MAX=1300

def density_check():
    al=I(F(2,3)); q=I(F(13,4))
    w=I(1); z=1/al
    for j in range(1,5):
        w=w*(q-(j-1))/(al*h)
        z+=w/al
    B=2*(I('11.0755')*exp(q*ln(h)-al*h)*z+
           I('3.1321')*exp(-h)*(h*h+2*h+2))
    assert B.below('.010443624')
    assert (8*h/3+2*ln(h)+(I(F(8,3))+2/h)/(I(F(7,15))-I('3.4')/h)).below(92)
    t=I(100)
    assert exp(kap*t).above(100)
    assert ((exp(t/2)-2)/5-exp(kap*t)).above(0)
    for k in (kap,F(1,3)):
        for s,_,_,_ in rows:
            s=I(s);q=5-2*s;al=(8*s-5)/3
            D=al-q/(k*t)
            assert D.above(0)
            assert (q/(k*t*t)/D).below('.01')
    print('Spectral input margins, height and K: OK',flush=True)

def B4(s,c,d):
    al=I((8*s-5)/3); q=I(5-2*s)
    w=I(1); z=1/al
    for j in range(1,5):
        w=w*(q-(j-1))/(al*h)
        z+=w/al
    return 2*(I(c)*exp(q*ln(h)-al*h)*z+I(d)*exp(-h)*(h*h+2*h+2))

@lru_cache(None)
def slopes():
    # FKS Table 8 first block: first number pair is the [.75,.80] row.
    spectral_rows=[
        ('.78','.80','7.7979','4.1006'),
        ('.80','.81','8.1610','3.6926'),
        ('.81','.82','8.5373','3.6126'),
        ('.82','.83','8.9269','3.5326'),
        ('.83','.84','9.3298','3.4526'),
        ('.84','.85','9.7461','3.3725'),
        ('.85','.86','10.1759','3.2924'),
        ('.86','.87','10.6191','3.2123'),
        ('.87','.875','11.0755','3.1321')]
    def upward(s,c,d):
        N=10**9
        return F(-(-B4(s,c,d).b*N//S),N)
    pieces=[];cur=None
    for al,ar,c,d in spectral_rows:
        al,ar=F(al),F(ar)
        n=5
        for j in range(n):
            l=al+(ar-al)*j/n;u=al+(ar-al)*(j+1)/n
            C=upward(l,c,d);D=upward(u,c,d)
            assert C>D
            # The monotone envelope has no downward jump here.
            assert cur is None or C>=cur
            cur=C if cur is None else cur
            if cur>D:
                m=(C-D)/(u-l)
                pieces.append((u-(cur-D)/m,u,m))
                cur=D
    assert cur==F('.010443624')
    return pieces

def zg(v):
    return K+sum(m*exp((u-b)*v)*(1-exp((l-u)*v))/v for l,u,m in slopes())

def choose(x,y):
    # Enclosure of analytic min, even if interval arguments overlap.
    return I(min(x.a,y.a),min(x.b,y.b),True)

def dg(v):
    y=kap*v
    return ((I('.026')*exp(-3*v/8)+I('.013')*exp(-7*v/40))*v*v
            +W('.70',h,'6.1727','4.4992')*exp(-v/8)
            +W('.75',h,'7.7979','4.1006')*exp(-I('.095')*v)
            +I('2.091')*v*exp(-I('.275')*v)
            +I('1.000000147')*exp(-3*v/8)+I('1.78')*exp(-13*v/24)
            +sum(W(s,y,c,d)*exp((F(t)-b)*v) for s,t,c,d in rows))

def met(v):
    v=I(v); r=exp(-v/8);Z=zg(v);d=choose(dg(v),dc(v))
    bs=Z+9*d
    bh=Z+(9+8/v)*d+3*exp(-7*v/8)
    assert (1-bh*r/v).above(0)
    return bs,bh/(1-bh*r/v)

def qscaled(v):
    return zg(v)*(1+2/(H*v))+(1+4/v)*choose(dg(v),dc(v))+I('3e-16')*v*exp(100-7*v/8)

def aN(v,n):
    return sum(f(i)/v**i for i in range(n+1))

def uN(v,n):
    return aN(v,n)+3*f(n+1)/v**(n+1)

def anc(n):
    t=2*n+5
    jmax=6*t
    z=I(0);w=I(1)
    for j in range(1,jmax+1):
        w=w*t/j
        z+=w/j
    ei=I(-1,1)+ln(t)+z+I(0,F(2*t**(jmax+1),f(jmax+1)))
    assert (ei-exp(t)/t*aN(I(t),n)).above(0)
    assert (ei-exp(t)/t*uN(I(t),n)).below(0)
    return t

def poly(n):
    cs=[sum(f(i)*comb(j,i) for i in range(min(n,j)+1)) for j in range(2*n+3)]
    u=[f(i) for i in range(n+1)]+[3*f(n+1)]
    for i,x in enumerate(u):
        for j,y in enumerate(u):cs[i+j]-=x*y
    assert cs[:6]==[0,0,0,0,1,14]
    assert all(c>0 for c in cs[4:n+1])
    return cs

@lru_cache(None)
def shifted(v):
    y=I(v-1)
    return exp(-y/8)*qscaled(y)

def model(v,n,cs,k,j,c):
    # Remainder beyond degree j controlled by preserving only the
    # leading positive coefficients and bounding negative ones.
    assert max(4,k)<=j<=n and (c is None or F(c)<=cs[k])
    r=shifted(v)
    v=I(v)
    ne=sum((-cs[i]/v**(i-j) for i in range(j+1,len(cs)) if cs[i]<0),I(0))
    rhs=sum(cs[i]*v**(j-i) for i in range(k,j+1))
    rhs-=ne
    v0=v-1
    loss=v**j*r*(v/v0+2*uN(v,n)+r)
    return rhs-I(cs[k] if c is None else c)*v**(j-k)-loss

def first(n,cs,k,j,c,lo):
    lo=max(lo,101,8*j+1,2*n+6)
    assert model(MAX,n,cs,k,j,c).above(0)
    hi=MAX
    while lo<hi:
        m=(lo+hi)//2
        if model(m,n,cs,k,j,c).above(0):hi=m
        else:lo=m+1
    assert model(lo,n,cs,k,j,c).above(0)
    return lo

def closed(lo,hi,c,side=False,var=False):
    from cert import gl,rloss
    lo,hi=F(lo),F(hi)
    if side:
        assert exp(I(hi)).below(139*10**15)
    assert lo>=36
    def cell(l,u):
        if (gl(l,u)-rloss(l,u,side)-I(c)-(14/I(l) if var else 0)).above(0):
            return 1
        assert u-l>F(1,100000),(l,u,c)
        m=(l+u)/2
        return cell(l,m)+cell(m,u)
    print('R closed',lo,hi,c,side,var,cell(lo,hi),flush=True)

def early():
    # Extend retained margins left or right, or bridge to a stronger
    # retained whole ray. Branches and coverage detailed in repair.md.
    closed('36.713','36.72','.001',True)
    closed('36.717','36.72','.003',True)
    closed('36.72','36.74','.004',True)
    closed('36.737','36.74','.013',True)
    closed('36.74','36.80','.014',True)
    closed('36.793','36.80','.040',True)
    closed('36.80','36.88','.043',True)
    closed('36.88','37','.080',True)
    closed('37','39.47','.137',True)
    closed('37.042','39.47','.155',True)
    closed('39.32','39.47','.85',True)
    closed('39.47','40','.155')
    closed('42.635','42.65','1')
    closed('47.17','47.25','1',var=True)

def main():
    density_check()
    for v,c in [(100,'.329'),(115,'.072'),(123,'.050'),(130,'.0365'),
                (150,'.02509'),(175,'.02033'),(182,'.01958'),(183,'.0195'),(184,'.01938'),(185,'.01928'),
                (189,'.01893'),(190,'.01885'),(200,'.018097'),(250,'.01579'),
                (400,'.013283'),(1000,'.011456'),(5000,'.010637'),
                (20000,'.010492'),(100000,'.010454')]:
        p,q=met(v)
        assert p.below(c) and q.below(c),(v,c,p,q)
        print('M',v,c,'OK',flush=True)
    v=I(189)
    assert (I('.01893')*exp(-v/8)).below('1.05e-12')
    assert (I('.01893')*v**2*exp(-v/8)).below('.0391')
    assert (I('.01938')*exp(-I(184)/8)).below('2.10e-12')
    early()
    n=32
    cs=poly(n)
    print('Ramanujan anchor',anc(n),flush=True)
    for k,c in [(6,0),(6,40),(6,'97.5'),(6,143)]+[(k,None) for k in range(6,31)]:
        outcomes=[(first(n,cs,k,j,c,175),j) for j in range(k if c is not None else k+1,min(k+5,n)+1)]
        v,j=min(outcomes)
        print('R',k,'exact' if c is None else c,v,j,flush=True)
    print('R',31,'exact',first(n,cs,31,32,None,175),32,flush=True)
    ratio=F(cs[31],2)
    print('R',31,'half',first(n,cs,31,32,ratio,175),32,flush=True)
    print('R',32,'half',first(n,cs,32,32,F(cs[32],2),175),32,flush=True)
if __name__=='__main__':
    main()
