
"""Exact directed rational Gaussian certificate, Python standard library only."""
from fractions import Fraction as Q
from math import comb,gcd,lcm
from pathlib import Path
import json,sys

def atan(q,n=75):
    s=sum(Q((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n))
    t=s+Q((-1)**n,(2*n+1)*q**(2*n+1))
    return min(s,t),max(s,t)

L5,U5=atan(5); L239,U239=atan(239)
PL,PU=16*L5-4*U239,16*U5-4*L239
SL=Q('1.77245385090551602729816748334114518279754945612238')
SU=SL+Q(1,10**50)
assert SL**2<PL<PU<SU**2
S=10**110

def fixed(lo,hi):
    return lo*S//1, -((-hi*S)//1)

def expminus(r):
    """exp(-r), r >= 0. Exact small-range Taylor, then interval squaring."""
    assert r>=0
    k=0
    while r>1: r/=2; k+=1
    t=s=Q(1)
    for j in range(1,102):
        t*=-r/j
        s+=t
    lo,hi=fixed(s,s-t*r/102)
    for _ in range(k):
        lo,hi=lo*lo//S, (hi*hi+S-1)//S
    return Q(lo,S),Q(hi,S)

def erfprim(x):
    if x>=10:
        return SL/2-expminus(x*x)[1]/(2*x), SU/2
    if not x: return Q(0),Q(0)
    r=x*x
    lo,hi=fixed(x,x)
    al,ah=lo,hi
    j=0
    while True:
        j+=1
        z=r*Q(2*j-1,j*(2*j+1))
        lo,hi=lo*z//1, -((-hi*z)//1)
        if hi<10**30 and j>r:
            # Alternating remainder lies between zero and this next term.
            if j%2: al-=hi
            else: ah+=hi
            break
        if j%2: al-=hi; ah-=lo
        else: al+=lo; ah+=hi
    return Q(al,S),Q(ah,S)

def fourier(p):
    n=(len(p)-1)//2
    g=[Q(0)]*(2*n+1)
    h=[1]
    for j in range(2*n+1):
        if j%2==0:
            t=p[j]*(-1)**(j//2)/2**j
            for k,a in enumerate(h): g[k]+=a*t
        h=[-((k+1)*h[k+1] if k+1<len(h) else 0)+(2*h[k-1] if k else 0)
           for k in range(len(h)+1)]
    return g

def segments(p,a,b):
    """Bernstein intervals via dyadic subdivision; scale keeps coefficients exact."""
    d=len(p)-1
    mono=[(b-a)**j*sum(p[k]*comb(k,j)*a**(k-j) for k in range(j,d+1)) for j in range(d+1)]
    B=[sum(mono[j]*Q(comb(i,j),comb(d,j)) for j in range(i+1)) for i in range(d+1)]
    denom=lcm(*(v.denominator for v in B))
    todo=[(a,b,[int(v*denom) for v in B],denom,0)]
    seg=[]
    while todo:
        l,r,bs,s,dep=todo.pop()
        bl,bu=min(bs),max(bs)
        sign=1 if bl>=0 else -1 if bu<=0 else 0
        if sign or dep==48:
            cap=Q(max(-bl,bu),s) if not sign else Q(0)
            if seg and sign and seg[-1][2]==sign:
                seg[-1]=(seg[-1][0],r,sign,cap)
            else: seg.append((l,r,sign,cap))
            continue
        ls,rs=[bs[0]<<d],[bs[-1]<<d]
        for j in range(d-1,-1,-1):
            bs=[x+y for x,y in zip(bs,bs[1:])]
            ls.append(bs[0]<<j); rs.append(bs[-1]<<j)
        m=(l+r)/2
        todo.append((m,r,rs[::-1],s<<d,dep+1))
        todo.append((l,m,ls,s<<d,dep+1))
    return seg

def signedprim(p,x):
    # ∫_0^x y^{2j}e^{-y²}dy = a_j I0(x) - b_j(x)e^{-x²}.
    a,b=Q(1),Q(0)
    A,B=p[0],Q(0)
    for j in range(1,(len(p)+1)//2):
        q=Q(2*j-1,2)
        a*=q
        b=q*b+x**(2*j-1)/2
        A+=p[2*j]*a; B-=p[2*j]*b
    l,u=erfprim(x)
    el,eu=expminus(x*x)
    return min(A*l,A*u)+min(B*el,B*eu), max(A*l,A*u)+max(B*el,B*eu)

def tail(p,r):
    # ∫_r^∞ exp(-y²)dy ≤ exp(-r²)/(2r); recur with absolute coefficients.
    T,B=1/(2*r),abs(p[0])/(2*r)
    for j in range(1,(len(p)+1)//2):
        T=Q(2*j-1,2)*T+r**(2*j-1)/2
        B+=abs(p[2*j])*T
    return B*expminus(r*r)[1]

def int_cap(p,a,r,wing):
    ans=tail(p,r)
    for l,u,s,c in segments(p,a,r):
        if wing and s<0: continue
        if s==0:
            ans+=c*(u-l)*expminus(l*l)[1]
        else:
            xl,xh=signedprim(p,l); yl,yh=signedprim(p,u)
            ans+= yh-xl if s>0 else xh-yl
    return (2/SL)*ans

def capdec(q,n=12):
    return Q(-((-q*10**n)//1),10**n)

def verify(file,A,target,r=Q(20),scale=Q(1)):
    coeff=list(map(Q,json.loads(Path(file).read_text())))
    p=[t for c in coeff for t in (c,Q(0))][:-1]
    g=fourier(p)
    assert all(not g[j] for j in range(1,len(g),2))
    assert fourier(g)==p
    M=capdec(int_cap(p,Q(0),r,False)/scale)
    J=capdec(int_cap(g,SL/scale,r,True))
    d=p[0]-A*J
    print(file, 'M ≤',float(M),'J ≤',float(J),'F(0) =',p[0])
    if d>0:
        print('ratio ≤',float(capdec(M/d)),'A sufficient ≤',float((p[0]-Q(5,4)*M)/J))
    if target is not None: assert d>0 and M<target*d
    return M,J,p[0]

if __name__=='__main__':
    verify(sys.argv[1],Q(sys.argv[2]),Q(sys.argv[3]) if len(sys.argv)>3 else None,scale=Q(sys.argv[4]) if len(sys.argv)>4 else Q(1))
