#!/usr/bin/python3.10
# Directed Decimal interval certificates. See notes.md for the arithmetic contract.
from decimal import Decimal as D, localcontext, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from math import factorial, comb
from fractions import Fraction as Q
PREC=53
def rnd(mode, f):
    with localcontext() as c:
        c.prec=PREC
        c.rounding=mode
        return f()
def lo(f): return rnd(ROUND_FLOOR,f)
def hi(f): return rnd(ROUND_CEILING,f)
class I:
    def __init__(self,x,y=None):
        if isinstance(x,I):
            self.a,self.b=x.a,x.b
        elif isinstance(x,Q):
            a,b=D(x.numerator),D(x.denominator)
            self.a,self.b=lo(lambda:a/b),hi(lambda:a/b)
        else:
            self.a,self.b=D(x),D(x if y is None else y)
    def __add__(x,y):
        y=I(y); return I(lo(lambda:x.a+y.a),hi(lambda:x.b+y.b))
    __radd__=__add__
    def __neg__(x): return I(x.b.copy_negate(),x.a.copy_negate())
    def __sub__(x,y):return x+-I(y)
    def __rsub__(x,y):return I(y)+-x
    def __mul__(x,y):
        y=I(y); z=[(a,b) for a in (x.a,x.b) for b in (y.a,y.b)]
        return I(min(lo(lambda:a*b) for a,b in z),max(hi(lambda:a*b) for a,b in z))
    __rmul__=__mul__
    def __truediv__(x,y):
        y=I(y);assert y.a*y.b>0
        return x*I(lo(lambda:1/y.b),hi(lambda:1/y.a))
    def __rtruediv__(x,y):return I(y)/x
    def __pow__(x,p):
        if not isinstance(p,int): return (I(p)*x.log()).exp()
        if p<0:return 1/(x**(-p))
        r=I(1)
        while p:
            if p%2:r=r*x
            p//=2
            if p:x=x*x
        return r
    def transcend(x,which):
        with localcontext() as c:
            c.prec=PREC
            c.rounding=ROUND_HALF_EVEN
            return I(getattr(x.a,which)().next_minus(),getattr(x.b,which)().next_plus())
    def exp(x):return x.transcend('exp')
    def log(x):assert x.a>0;return x.transcend('ln')
    def __repr__(x):return f'[{x.a},{x.b}]'
def mini(*xs):
    return I(min(x.a for x in xs),min(x.b for x in xs))
def bnd(x,y,t):
    'e^(-t*x) upper endpoint for t positive'
    return (-I(t)*x).exp()

# c1,c2 padded on the safe side from FKS Table 8 (0.77 block).
rows=[(70,'6.173','4.500'),(75,'7.798','4.101'),(80,'8.1611','3.693'),
      (81,'8.538','3.613'),(82,'8.927','3.533'),(83,'9.330','3.453'),
      (84,'9.747','3.373'),(85,'10.176','3.293'),(86,'10.620','3.213'),
      (87,'11.076','3.133')]
h=I(3000000000000).log()
def count_weight(s):
    _, a, b=max(r for r in rows if Q(r[0],100)<=s)
    k=Q(8,3)*(1-s); q=5-2*s
    # integral bound on (h+v)^q, by concavity after extracting (h+v)^3
    d=1-k
    J=sum(comb(3,j)/h**j*(factorial(j)/I(d)**(j+1)+(q-3)*factorial(j+1)/(h*I(d)**(j+2))) for j in range(4))
    K=h*h+2*h+2
    return 2*(I(a)*((-I(d)*h).exp())*h**q*J+I(b)*K/3000000000000)
Q0=Q(7,8);Q1=Q(27,32)
def spec(beta,start=Q(3,4)):
    cuts=[i*Q(1,2000) for i in range(int(start*2000),int(beta*2000)+1) if i*Q(1,2000)<beta]
    # fix decimal outward upper bounds as exact rational constants
    C=[]
    for s in cuts:
        # either bound is legal at a listed join; use next interval, or left limit 
        # across join via sparsely spaced grid + downward running min
        w=count_weight(s).b
        if C:w=min(C[-1],w)
        C.append(w)
    return [(I(117),Q(1,2),0),(I(13),Q(1,2),1),(I(Q(1,25)),1-start,2),(I(2),1-start,0)]+[
        (I(Q(c)-Q(d)),1-a,0) for c,d,a in zip(C,C[1:]+[D(0)],cuts[1:]+[beta])]
S0,S1=spec(Q0),spec(Q1)
CH=[(I('0.000000000001047198'),Q(0),0),(I('113.67'),Q(1,2),0)]
DP=[(I(Q(1,64)),Q(5,32),2)]
powers=[(I('1.000000147'),Q(1,2),0),(I('1.78'),Q(2,3),0)]
def ev(S,L,j=0):
    return sum(c*I(L)**(k+j)*(-I(a)*L).exp() for c,a,k in S)
# Pointwise weighted losses divided by x^2/L^6. For efficient block checks
# cache L^4 times each pi-normalized error at SAME argument.
from functools import lru_cache
J=Q(58)
@lru_cache(None)
def psierr(v,mode):
    old=(2*I(v)**5/25)*(-I(v)+29).exp()
    def calc(S):
        return sum(c*I(v)**(4+k)*(-I(a)*v).exp()*(1+1/(I(v)*(1-a-2/J))) for c,a,k in S+powers)+old
    if v<=58:
        return (I(v)**6+2*I(v)**5)*(-I(v)/2).exp()/25
    p=mini(calc(CH),calc(S0))
    if mode: p=mini(p,calc(S1))
    return p
@lru_cache(None)
def monobranch_bounds(l,u,mode):
    # all used L^4-transported terms decrease beyond L=58 except CH's constant-exp branch.
    # CH's transported near-constant terms taken at u, its decaying terms at l.
    def single(v,w,S):
        return sum(c*I(w if a==0 else v)**(4+k)*(-I(a)*(w if a==0 else v)).exp()*
                   (1+1/(I(w if a==0 else v)*(1-a-2/J)))
                   for c,a,k in S+powers)+(2*I(v)**5/25)*(-I(v)+29).exp()
    if u<=58:return psierr(l,0)
    if l>=58:
        p=mini(single(l,u,CH),single(l,l,S0))
        if mode:p=mini(p,single(l,l,S1))
        return p
    return I(0,max(monobranch_bounds(l,58,mode).b,monobranch_bounds(Q(58),u,mode).b))
def g(n):
    return sum(factorial(n)//factorial(j)-factorial(j)*factorial(n-j) for j in range(n+1))
def Hmain(L,N):
    return sum(I(g(n))/I(L)**(n-4) for n in range(4,N+1))
def Alim(L):return 1+1/I(L)+3/I(L)**2
def loss(l,u,mode,signed=True):
    d=monobranch_bounds(l,u,mode)
    m=monobranch_bounds(l-1,u-1,mode)*(I(l)/(l-1))**5
    # Theta below x throughout the past in the signed finite branch.
    if signed and u<=Q('39.47'):return m
    return m+2*Alim(l)*d+d*d/I(l)**4
def Finit(L):
    b=I(600).log()
    ps=[p for p in range(2,601) if all(p%d for d in range(2,p) if d*d<=p)]
    c=len(ps)+(600-sum(I(p).log() for p in ps))/b
    def integral(s):
        # log(s)+sum s^n/(n n!), antiderivative of exp(s)/s
        assert s.a>0 and s.b<=40
        n=190
        z=s.log()+sum(s**j/(j*factorial(j)) for j in range(1,n+1))
        return z+I(0,(2*s**(n+1)/((n+1)*factorial(n+1))).b)
    return c+integral(I(L))-integral(b)
def main_ode(N,L0=34):
    for n in range(4,N+1):assert g(n)>0
    A=lambda L: I(L)*(-I(L)).exp()*Finit(L)
    A0=A(L0)
    P=sum(I(factorial(n))/I(L0)**n for n in range(N+1))
    assert P.b < A0.a and A0.b < Alim(L0).a
    C=I(L0)/(L0-1)*A(L0-1)-A0*A0
    assert (Hmain(L0,N)/I(L0)**4).b < C.a
    # Triangular polynomial source certificate.
    a=[0,0]+[factorial(n)-1 for n in range(2,N)]+[factorial(N)-2]
    d=[sum(a[i]*a[n-i] for i in range(len(a)) if 0<=n-i<len(a)) for n in range(2*N+1)]
    p=[d[j]-(d[j-1] if j else 0) for j in range(len(d))]+[-d[-1]]
    for n in range(4,N+2):
        p[n]-=g(n) if n<=N else 0
        if n>=5:p[n]+=n*g(n-1)
    assert all(v==0 for v in p[:N+1])
    assert p[N+1]+sum(Q(min(c,0),L0**(j-N-1)) for j,c in enumerate(p) if j>N+1)>0
    print('ODE order',N,'at',L0, 'verified')
def finite(l,u,N,mode,target,step=Q(1,8),start_n=0):
    # target is polynomial in 1/L, with nonnegative coefficient list
    diff=[(g(j+4) if j+4<=N else 0)-(target[j] if j<len(target) else 0)
           for j in range(max(N-3,len(target)))]
    m=D('Infinity'); at=None
    while l<u:
        r=min(u,l+step)
        low=sum(I(c)/I(r if c>=0 else l)**j for j,c in enumerate(diff))-loss(l,r,mode)
        if low.a<m:m,at=low.a,l
        l=r
    print('finite',mode,target,'slack',f'{m:.8E}','at',at)
    assert m>0
def tail(l,N,mode,target,verbose=True):
    # by L>=l, L^4 loss <= l^4 loss provided l>= threshold of each exponential term.
    # All target coefficients except radius correction are nonnegative residuals.
    j=next(j for j in range(N-3) if (g(j+4)-(target[j] if j<len(target) else 0))>0)
    sub=target+[0]*(N-3-len(target))
    assert all(g(n)-sub[n-4]>=0 for n in range(4,N+1))
    assert l-1>=Q(6+j)/Q(1,8) and l>=59
    # use just spectral branch for tail, also when CH happens to be smaller
    def one(v):
        S=S1 if mode else S0
        return sum(c*I(v)**(4+k)*(-I(a)*v).exp()*(1+1/(I(v)*(1-a-2/J))) for c,a,k in S+powers)+(2*I(v)**5/25)*(-I(v)+29).exp()
    d=one(l);m=one(l-1)*(I(l)/(l-1))**5
    assert ((m+2*Alim(l)*d+d*d/I(l)**4)*I(l)**j).b < I(g(j+4)-sub[j]).a
    if verbose: print('tail',mode,'L>=',l,'leading residual degree',j)

targets=[
 (0,[0], '39.7', 240),(0,[Q(1,2)],'40.9',240),(0,[Q(9,10)],'42.6',240),
 (0,[1],'43.2',240),(0,[1,14],'47.7',240),
 (0,[1,14,5],'48',240),(0,[1,14,7],'49.4',240),(1,[1,14,78],'49.4',240),
 (0,[1,14,100],'200.1',250),(1,[1,14,100],'172',230),
 (0,[1,14,145],'221',270),(1,[1,14,145],'187',240),
 (0,[1,14,145,1412],'254',310),(1,[1,14,145,1412],'211.5',270),
 (0,[1,14,145,1412,13985],'288.5',335),(1,[1,14,145,1412,13985],'237',300),
 (0,[1,14,145,1412,13985,145450],'323.5',380),(1,[1,14,145,1412,13985,145450],'263',320),
]
def ram():
    main_ode(27)
    assert I('39.47').exp().b<D('139000000000000000')
    assert I(58).exp().b<D('21690000000000000000000000')
    assert (I('0.125')*I(25)).b<D('3.14159265358979323846') # 8pi>25
    finite(Q('37.2'),Q('39.47'),27,0,[0],Q(1,32))
    finite(Q('38.5'),Q('39.47'),27,0,[Q('0.5')],Q(1,32))
    print("early signed finite branch verified")
    for mode,target,l,u in targets:
        l,u=Q(l),Q(u)
        # align remaining checks on a common rational dyadic mesh
        step=Q(1,8)
        v=min(u,Q(l//step+1)*step)
        finite(l,v,27,mode,target,step)
        if v<u:finite(v,u,27,mode,target,step)
        tail(u,27,mode,target)
    high()
def high():
    for N in range(10,27):
        t=[g(n) for n in range(4,N+1)]
        out=[]
        for m in (0,1):
            # search the first half-unit onset satisfying this monotone
            # sufficient tail condition, not necessarily the best onset.
            j=N-3
            l,r=2*(8*(6+j)+1),4000
            while l<r:
                mid=(l+r)//2
                try:tail(Q(mid,2),27,m,t,False); r=mid
                except AssertionError:l=mid+1
            tail(Q(r,2),27,m,t,False)
            out.append(str(Q(r,2)))
        print("high profile",N,*out)
if __name__=='__main__':
    import sys
    if sys.argv[1:]==['--high']:high()
    else:ram()
