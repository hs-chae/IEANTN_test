'''Exact rational checker for polynomial-Gaussian witnesses. Python 3.10 stdlib.'''
from fractions import Fraction as Q
from math import gcd,lcm,isqrt,ceil
from functools import lru_cache
import json,sys

# Machin: arctan(1/1)=4 arctan(1/5)-arctan(1/239).
def atan_inv(n,k):
    s=sum((Q((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(2*k)),Q())
    return s,s+Q(1,(4*k+1)*n**(4*k+1))
p,q=atan_inv(5,100); r,s=atan_inv(239,40)
PI=(16*p-4*s,16*q-4*r)
S=10**140
def fl(x):return x.numerator//x.denominator
def sqrtpi():
    pl,ph=PI
    return Q(isqrt(fl(pl*S*S)),S),Q(1+isqrt(fl(ph*S*S)),S)
SQ=sqrtpi()

def plus(A,B):return A[0]+B[0],A[1]+B[1]
def scale(A,q):
    a,b=A
    return (q*a,q*b) if q>=0 else (q*b,q*a)
def neg(A):return (-A[1],-A[0])
def times(A,B):
    x=[a*b for a in A for b in B];return min(x),max(x)
def mid(A):return (A[0]+A[1])/2

@lru_cache(None)
def gauss(u):
    # For each k, t_k=(u^2)^k/k!, t_k bounds in units 1/S.
    z=u*u
    n,d=z.numerator,z.denominator
    k=0;l=h=S
    al=ah=bl=bh=0
    while True:
        dl=2*k+1
        if k%2:
            al-=h;ah-=l;bl-=(h+dl-1)//dl;bh-=l//dl
        else:
            al+=l;ah+=h;bl+=l//dl;bh+=(h+dl-1)//dl
        k+=1
        l=l*n//(d*k)
        h=(h*n+d*k-1)//(d*k)
        if k*d>=n and h<=2:
            # Decreasing magnitudes from this term: alternating remainders.
            al-=h;ah+=h;bl-=h;bh+=h
            break
    return (Q(al,S),Q(ah,S)),(u*Q(bl,S),u*Q(bh,S))

def trim(p):
    p=list(p)
    while p and not p[-1]:p.pop()
    return p
def primitive(p):
    den=lcm(*(v.denominator for v in p))
    r=[int(v*den) for v in p]
    g=gcd(*r)
    return [v//g for v in r] if g else []
def rem(a,b):
    a=list(map(Q,a))
    while len(a)>=len(b):
        c=a[-1]/b[-1];i=len(a)-len(b)
        for j,x in enumerate(b):a[i+j]-=c*x
        a=trim(a)
    return a
def sturm(p):
    a=primitive(p)
    b=primitive([i*a[i] for i in range(1,len(a))])
    out=[a]
    while b:
        out.append(b);c=primitive([-v for v in rem(a,b)]);a,b=b,c
    # Candidate-specific check rules out repeated roots, not assumed.
    assert len(out[-1])==1
    return out
def ev(a,x):
    s=Q()
    for c in reversed(a):s=s*x+c
    return s
def sg(z):return (z>0)-(z<0)
def vh(a,z):
    if z is None:return sg(a[-1])
    n,d=z.numerator,z.denominator
    f=a[-1];h=d
    for b in reversed(a[:-1]):
        f=f*n+b*h;h*=d
    return sg(f)
def var(seq,u):
    z=None if u is None else u*u
    a=[x for p in seq if (x:=vh(p,z))]
    return sum(x!=y for x,y in zip(a,a[1:]))
def brackets(p,start):
    seq=sturm(p)
    a=start;b=Q(16)
    assert a<b and ev(p,a*a)!=0 and ev(p,b*b)!=0
    u,v=var(seq,a),var(seq,b)
    assert var(seq,None)==v
    L=[(a,b,u,v)];out=[]
    while L:
        a,b,u,v=L.pop()
        if u==v:continue
        assert u>v
        if u-v==1 and b-a<Q(1,10**45):
            out.append((a,b))
            continue
        c=(a+b)/2
        assert ev(p,c*c)!=0
        m=var(seq,c);assert v<=m<=u
        L.extend([(c,b,m,v),(a,c,u,m)])
    return out

def primitive_gauss(p):
    R=[Q()]*len(p)
    T=Q()
    for k in reversed(range(1,len(p))):
        T+=p[k]
        R[k]=-T/2
        T*=(2*k-1)*Q(1,2)
    T+=p[0]
    def f(u):
        if u is None:return scale(SQ,T/2)
        e,I=gauss(u)
        return plus(scale(e,u*ev(R[1:],u*u)),scale(I,T))
    return f

def integral(p,start,absolute):
    sl=brackets(p,start)
    F=primitive_gauss(p)
    ans=Q(),Q();lo=start
    for a,b in sl+[(None,None)]:
        z=lo+1 if a is None else (lo+a)/2
        sign=sg(ev(p,z*z));assert sign
        if absolute or sign>0:
            ans=plus(ans,scale(plus(F(a),neg(F(lo))),sign))
        if a is not None:
            # Bound entire contribution of root bracket by a rectangle.
            e,_=gauss(a)
            eps=(b-a)*e[1]*ev([abs(x) for x in p],b*b)
            ans=plus(ans,(Q(),eps))
        lo=b
    return times(ans,(2/SQ[1],2/SQ[0])),len(sl)

def lag(n):
    # L_n^(-1/2)(2 z): asc coefficients; binomial expansion, rational.
    a=Q(1)
    for i in range(1,n+1):a*=Q(2*i-1,2*i)
    p=[a]
    for i in range(n):p.append(-p[-1]*Q(4*(n-i),(i+1)*(2*i+1)))
    return p

def poly(x):
    p=[Q()]*(len(x));q=p[:]
    for n,r in enumerate(x):
        for k,a in enumerate(lag(n)):
            p[k]+=r*a;q[k]+=(-1)**n*r*a
    return p,q

def print_interval(name,I,d=17):
    print(name,fl(I[0]*10**d),ceil(I[1]*10**d),'in units',f'1e-{d}')
def main(path):
    data=json.load(open(path)); x=list(map(Q,data['laguerre']))
    p,q=poly(x)
    assert p[0]==1
    M,n=integral(p,Q(),True)
    W0,m=integral(q,Q(fl(SQ[0]*10**30),10**30),False)
    # Lower endpoint has moved down by < 2e-30; restore valid lower leak bound.
    a=Q(fl(SQ[0]*10**30),10**30); b=a+Q(2,10**30)
    assert a<=SQ[0] and SQ[1]<=b
    eps=(b-a)*gauss(a)[0][1]*ev([abs(t) for t in q],b*b)*2/SQ[0]
    W=(max(Q(),W0[0]-eps),W0[1])
    print(path,n,m)
    print_interval('M',M);print_interval('J',W)
    A=Q(data['A'])
    assert A>=1 and 1-A*W[1]>0
    R=(M[0]/(1-A*W[0]),M[1]/(1-A*W[1]))
    print_interval('ratio',R)
    print_interval('critical A at 0.8',((1-5*M[1]/4)/W[1],(1-5*M[0]/4)/W[0]))
    if 'target' in data:assert R[1]<Q(data['target'])

if __name__=='__main__':
    for path in sys.argv[1:]:main(path)
