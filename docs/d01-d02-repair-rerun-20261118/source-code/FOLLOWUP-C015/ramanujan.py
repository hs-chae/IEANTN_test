from analytic import *
from math import factorial as fac
N=22
def barrier(L,n=N):
    return sum(I(fac(k))/L**(k+1) for k in range(n))
def ei(L):
    L=I(L)
    t=I(1); v=gamma()+L.log()
    for j in range(1,201):
        t=t*L/j
        v+=t/j
    return v+bracket(0,t*L/201**2*2)
def boot():
    a=I(32); f=fac(N)
    A=ei(32)*ex(-a)
    assert low(A,barrier(a))
    assert low(barrier(a)+5*f/a**(N+1),A)
    # L=32: use coefficient 5.
    assert F(5)*(1-F(N+1,32))>1
U=[F(fac(k)) for k in range(N)]+[F(5)*fac(N)]
def coeff(j):
    left=sum(fac(k)*comb(j,k) for k in range(min(j,N-1)+1))
    return left-sum(U[k]*U[j-k] for k in range(len(U)) if 0<=j-k<len(U))
CO=[coeff(j) for j in range(2*N+1)]
assert CO[:4]==[0]*4
def liR(L):
    return sum(c/L**j for j,c in enumerate(CO[4:]) if c)
def fin(L):
    # Oscillatory integrated psi and explicit removal of higher powers.
    a=I(8)
    r=ex(-L/2)
    b8=ex(4)*(8**2+8)/(8*PI)
    j1=I('.12')*(2*r/L+L*ex(4-L)/64)
    j2=I('.000000000008')*(I('1.4')*ex(-L/8)/L+L*ex(7-L)/64)
    j3=(I('1.84')/8+b8)*L*ex(-L)
    vp=(4*I('1.000000147')*r+I('21.36')*ex(-2*L/3))/L
    h=L*L/(8*PI)*r
    if L.lo>=34*S:
        for ratio in [F(1,2),F(13,20)]+([F(2,5)] if L.lo>=35*S else []):
            c=optimized_ch(L,ratio=ratio)+I('1.000000147')*r+I('1.78')*ex(-2*L/3)
            h=I.raw(min(h.lo,c.lo),min(h.hi,c.hi))
    return h+j1+j2+j3+vp
def join(L,a,err,modes):
    a=I(a)
    def mode(v,c,g,k):return c*v**k*ex(-g*v)
    return sum(mode(L,*m) for m in modes)+(L/a)*ex(a-L)*(err+sum(mode(a,*m) for m in modes))+sum(mode(L,*m)*L/(a*a*(1-m[1])) for m in modes)
chm=[(I(b),F(0),0),(116,F(1,2),0),(I('1.78'),F(2,3),0)]
sm=[(I('.04'),F(1,5),2),(13,F(1,2),1),(I('1.000000147'),F(1,2),0),(I('1.78'),F(2,3),0)]+[(c,g,0) for c,g in HIG]
f58=fin(I(58))
def ch(L):return join(L,58,f58,chm)
ch100=ch(I(100))
def sp(L):return join(L,100,ch100,sm)
ch140=ch(I(140))
def ch2(L):return join(L,140,ch140,chm)
def rp(L):
    a=I(140)
    vals=[(layer(L,*m),m[1]) for m in LS]
    return join(L,140,ch140,sm[:4])+sum(v*(1+L/(a*a*(1-g))) for v,g in vals)+(L/a)*ex(a-L)*sum(layer(a,*m) for m in LS)
def err(L):
    # L is an interval; split if it crosses the piece boundaries.
    vals=[]
    for a,z,M in [(33,58,fin),(58,100,ch),(100,10000,ch),(100,10000,sp),(140,10000,ch2),(170,280,rp)]:
        if L.lo>=a*S and L.hi<=z*S:vals.append(M(L))
    assert vals
    return I.raw(min(v.lo for v in vals),min(v.hi for v in vals))
def loss(L, error=err):
    e=error(L-1)
    f=I(0) if L.hi*100<=4374*S else error(L)
    u=1/L
    p=sum(c*u**k for k,c in enumerate(U))
    return L**4*(L/(L-1)*e+f*(2*p+f))
def bound(L):return liR(L)-loss(L)
def prof(L,c):return sum(I(a)/L**j for j,a in enumerate(c))
def tail(B,c):
    L=I(B); d=len(c)-1
    co=CO[4:].copy()
    for j,a in enumerate(c): co[j]-=F(a)
    while co[d]==0: d+=1
    # Lower bound L^d*(liR-target) by its constant term,
    # plus every negative coefficient at B, dropping positive extra terms.
    assert all(v>=0 for v in co[:d])
    h=co[d]+sum(v/F(B)**(j-d) for j,v in enumerate(co) if j>d and v<0)
    # Exact rational majorization of sp, also when exp underflows fixed point.
    def up(x):return F(cv(x).hi,S)
    assert low(E,F(2718,1000))
    def ep(q):
        assert q>=0
        return F(1000,2718)**int(q)
    anc=up(ch100+thetaSpec(I(100)))
    def sup(X):
        return (F(X,100)*ep(X-100)*anc+
                sum(up(c)*X**k*ep(g*X)*(1+F(X,10000)/(1-g)) for c,g,k in sm))
    assert B-1>8*(8+d)
    p=sum(v/F(B)**k for k,v in enumerate(U))
    assert h>B**(4+d)*(F(B,B-1)*sup(B-1)+sup(B)*(2*p+sup(B)))
    print('tail',B,c)
def run(a,B,c,den=100,whole=True,error=err):
    a=F(a)
    assert (a*den).denominator==1
    co=CO[4:].copy()
    for j,m in enumerate(c):co[j]-=F(m)
    def test(a,b):
        u=bracket(a,b)
        v=sum(v/u**j for j,v in enumerate(co) if v)-loss(u,error)
        if low(v,0): return
        if b-a<=F(1,den*64):
            raise ValueError((a,b,v,c))
        m=(a+b)/2
        test(a,m); test(m,b)
    for j in range(int(a),B):
        if j==43 and a<F('43.74'):
            test(max(a,j),F('43.74')); test(F('43.74'),F(j+1))
        else: test(max(a,j),F(j+1))
    if whole: tail(B,c)
    print('profile',a,B,c,whole)
def endpoint():
    n=38358837682; m=14111427770
    assert low(I(n)/E,m) and low(m+1,I(n+1)/E)
    def r(x):
        x=I(x)
        return E*x/x.log()*632207037-1644673232**2
    assert low(0,r(n)) and low(r(n+1),0)
    t=I(n+1).log()
    assert low(E*632207037*(t-1)/t**2,67_000_000)
    assert low(I(11_500_000_000_000_000).log(),'36.98')
    assert low(19*I(10).log(),'43.74')
    a,b=F(n),F(n+1)
    for j in range(32):
        mid=(a+b)/2
        if low(r(mid),0):b=mid
        elif low(0,r(mid)):a=mid
        else:break
    print('real root in',a,b)
if __name__=='__main__':
    import sys
    endpoint()
    boot()
    if 'explore' in sys.argv:
        for L in [34,35,36,37,38,39,40,41,42,43,44,45,48,50,58,59,60,80,100,101,120,150,180,195,200,210,220,230,240,250,270,300,350,400,500,650]:
            print(L,bound(I(L)),liR(I(L)), (bound(I(L))-1-14/I(L))*L**2)
    else:
        for l,m in [
            ('36.54',('0.005',)), ('36.74',('0.1',)), ('37.77',('0.5',)),
            ('39.38',('0.9',)), ('40',(1,)),
            ('45',(1,9)), ('47.2',(1,14)),
            ('48.3',(1,13,100)), ('223',(1,14,145)), ('263',(1,14,145,1412)),
            ('320',(1,14,145,1412,13985))]:
            run(l,360,m,100)
        run('40.4',289,('1.05',),whole=False)
        run('48',180,(1,14,20),whole=False)
        run('45',80,('1.2',),whole=False)
        run('47.4',56,('1.3',),whole=False)
        for B,d in [(450,7),(620,9),(850,11),(1300,13),(2200,15),(4000,16)]:
            tail(B,CO[4:4+d+1])
