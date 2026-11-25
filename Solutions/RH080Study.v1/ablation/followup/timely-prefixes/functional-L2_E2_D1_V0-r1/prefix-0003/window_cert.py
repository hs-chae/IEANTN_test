
"""Exact directed arithmetic for rational affine windows and step-function duals.
Twiddle source: pinned Blanquer Robles supplement, certificates/certify_integer.py.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json,sys
from gauss_cert import PL,PU,capdec
sys.path.insert(0,'/corpus/literature/Blanquer_supplement/certificates')
from certify_integer import real_dft, twiddles, UNIT, positive_area

def checked_eps(G,B):
    assert G>=2 and G&(G-1)==0
    e=Q(12*G,UNIT)
    assert Q(4*G,UNIT)<Q(1,2) and (G.bit_length()-1)*e/2<Q(1,2)
    return 2*G*(e*B+Q(2,UNIT))

def normfft(values,scale,G):
    assert scale>0 and UNIT%scale==0 and 2*len(values)<=G
    a=[Q(x,scale) for x in values]
    def store(v):
        err=checked_eps(G,Q(2*sum(map(abs,v))-abs(v[0]),scale))
        return real_dft([x*(UNIT//scale) for x in v],G), -((-err*UNIT)//1)
    p,ep=store(values)
    q,eq=store([-j*j*x for j,x in enumerate(values)])
    j4=sum(j**4*abs(v) for j,v in enumerate(a))
    # |Q''|<=80 sum j^4|a_j|, local chord error <=10 j4/G².
    qcurv=-((-10*j4*UNIT/G**2)//1)
    sim=lin=locs=0
    for i in range(0,G,2):
        l,m,r=p[i],p[i+1],p[(i+2)%G]
        loc=40*(max(abs(q[i]),abs(q[i+1]),abs(q[(i+2)%G]))+eq+qcurv)
        # If both length-1/G chords have the same definite sign, use Simpson.
        if (min(l,m,r)-ep)*8*G**2>loc: sim+=l+4*m+r
        elif (-max(l,m,r)-ep)*8*G**2>loc: sim-=l+4*m+r
        else:
            lin+=abs(l)+2*abs(m)+abs(r)
            locs+=loc
    # Nodal error contributes ep/UNIT in total regardless of panel choice.
    return (Q(sim,3*G*UNIT)+Q(lin,2*G*UNIT)+Q(ep,UNIT)+
            Q(locs,6*G**3*UNIT)+Q(3200,180*G**4)*j4)

def readwin(file,G):
    data=json.loads(Path(file).read_text())
    m,s,a=data['m'],data['scale'],data['coefficients']
    assert 0<m<len(a) and len(a)<=10*m
    U=capdec(normfft(a,s,G),14)
    a=[Q(x,s) for x in a]+[Q(0)]
    F0=(a[0]+2*sum(a[1:]))/m
    J=2*sum(positive_area(a[j],a[j+1]) for j in range(m,len(a)-1))/m
    H=max(0,a[m])+sum(max(0,max(0,r)-max(0,l)) for l,r in zip(a[m:],a[m+1:]))
    A0=(abs(a[0])+2*sum(map(abs,a[1:])))/m
    vl=[m*(r-l) for l,r in zip(a,a[1:])]+[0]
    V0=2*sum(abs(r-l) for l,r in zip(a,a[1:]))
    V1=2*(abs(vl[0])+sum(abs(r-l) for l,r in zip(vl,vl[1:])))
    # μ2 upper bound: convex chord of endpoint magnitudes integrates exactly.
    mu2=Q(0)
    for j,(l,r) in enumerate(zip(a,a[1:])):
        mu2+=2*(abs(l)*(Q(j*j,2)+Q(j,3)+Q(1,12))
                 +abs(r)*(Q(j*j,2)+Q(2*j,3)+Q(1,4)))/m**3
    M=max(map(abs,a))
    R=Q(len(a)-1,m)
    return dict(m=m,R=R,U=U,F0=F0,J=J,H=H,A0=A0,V0=V0,V1=V1,mu2=mu2,M=M)

def sine_dft(values,G):
    c,s=twiddles(G)
    re,im=[0]*G,[0]*G
    for j,v in enumerate(values,1): re[j]=v; re[-j]=-v
    j=0
    for i in range(1,G):
        bit=G>>1
        while j&bit:
            j^=bit
            bit>>=1
        j^=bit
        if i<j: re[i],re[j]=re[j],re[i]
    w=2
    while w<=G:
        half=w//2; q=G//w
        for first in range(0,G,w):
            for k in range(half):
                i,j=first+k,first+k+half
                u,v=re[j],im[j]
                c0,s0=c[k*q],s[k*q]
                a,b=(c0*u-s0*v)//UNIT,(s0*u+c0*v)//UNIT
                re[i],re[j]=re[i]+a,re[i]-a
                im[i],im[j]=im[i]+b,im[i]-b
        w*=2
    return im

def dual(file,G,target=None):
    d=json.loads(Path(file).read_text()); m=d['m']; A=Q(d['A'])
    assert isinstance(m,int) and m>0 and A>=1
    v=list(map(Q,d['wing_heights']))
    assert all(1-A<=x<=1 for x in v)
    v=[Q(1)]*m+v
    jumps=[l-r for l,r in zip(v,v[1:]+[Q(0)])]
    assert len(jumps)*2<G
    coeff=[round(j*UNIT) for j in jumps]
    err=checked_eps(G,2*Q(sum(map(abs,coeff)),UNIT))+2*sum(abs(Q(c,UNIT)-j) for c,j in zip(coeff,jumps))
    L=abs(2*sum(v)/m)
    arr=sine_dft(coeff,G)
    # Compute all nonzero sampled |S(k)|/k with integer cross products.
    b,k0=max(((abs(arr[k]),k) for k in range(1,G//2+1)),key=lambda t:Q(*t))
    sample=max(L,(Q(b,k0*UNIT)+err)*G/(2*m*PL))
    moment=2*sum(abs(vj)*((j+1)**3-j**3) for j,vj in enumerate(v))/(3*m**3)
    cap=capdec(sample+5*moment*Q(m,G)**2,12)
    print('dual',file,'A=',A,'uniform cap',cap,'floor ≥',float(1/cap))
    if target is not None: assert cap<=target
    return cap

def lowerlog(x):
    """Log enclosure via 2 atanh((x-1)/(x+1)); reduction to [1,2)."""
    assert x>0
    def core(t):
        z=(t-1)/(t+1)
        s,u=Q(0),z
        for j in range(26):
            s+=u/(2*j+1); u*=z*z
        return 2*s,2*s+2*u/(53*(1-z*z))
    k=0
    while x>=2: x/=2; k+=1
    while x<1: x*=2; k-=1
    a,b=core(x); l,h=core(Q(2))
    return a+min(k*l,k*h), b+max(k*l,k*h)

def exp_pos_partial(x,n):
    t=s=Q(1)
    for j in range(1,n+1):
        t*=x/j
        s+=t
    return s

def margin(info,c,a,b=None,k=1,tau=Q(3,8)):
    """Proof premises and exact evaluation for a real slab or a ray, t=log x."""
    F0,J,U,H,M,R,A0,V0,V1,mu2=[info[x] for x in ['F0','J','U','H','M','R','A0','V0','V1','mu2']]
    assert Q(1,2)<=c<=1 and a>=42 and 1<=k<=16 and 0<tau<1
    assert 0<F0<=2 and 0<U<=2 and A0<=2 and M<=2 and V0<=10 and V1<=50 and R<=10
    assert exp_pos_partial(Q(21),70)>10**9
    assert exp_pos_partial(Q(20),70)>320000000
    dmax=Q(1,50000000); lmax=10*dmax
    # For z<=1e-6, exp(z) <= 1/(1-z).
    assert 4*(1+lmax/42)/(1-3*lmax/2)<Q('4.00001')
    assert Q(42,2)/10**9<dmax or exp_pos_partial(Q(21),70)>Q(42,2)/dmax
    assert Q(42)**2/4/10**9 < Q('0.000001')
    # Coarse analytic error proof, independent of witness except checked scalar caps.
    g1=(10*V1+2*V0)/(2*PL)
    st=dmax*(Q('.3')*g1+12*(2*PU*R*A0+g1))
    assert st<Q('0.0001')
    u0=Q(10)*dmax/(2*PL)
    assert 2*A0*u0*(1-lowerlog(u0)[0])<Q('0.00001')
    # Eq. (19) with support R in place of 5, t>=42.
    pot=M*(42+11*dmax)**2/(2*lowerlog(Q(2))[0]*10**9*(1-5*dmax))*(1+R*c*42/(2*(1-6*dmax)))
    assert pot<Q('.001')
    # The total pole loss (including d*sqrt(a)) is <1e-10 by t*d²
    # decreasing from t=42; trivial term <1e-8 (proof in text).
    assert 2*(lmax/2)**2/(1-lmax/2)*21<Q('1e-10')
    B=Q('4.00001')
    D=F0-B*J
    assert D>0
    _,logk=lowerlog(Q(k))
    denom=1-2*logk/a
    assert denom>0
    loss_k=B*J*c*logk/denom
    end_k=2*B*H/(k*denom)
    logtau_lo,logtau_hi=lowerlog(tau)
    gain=2*F0*tau*(1-logtau_hi)-40*mu2*tau**3*(Q(1,9)-logtau_lo/3)
    logmom=V1/(2*PL**2)-gain
    K=loss_k+end_k+logmom+Q('.0012')
    def endpoint(t):
        return (c*D-U)*t/2+U*lowerlog(c*t/2)[0]-K
    if b is None:
        assert c*D>=U
        lo=endpoint(a)
    else:
        assert b>=a
        lo=min(endpoint(a),endpoint(b))
    print(f'margin c={c}, t=[{a},{b}], block k={k}, positive lower bound {float(lo):.12g}')
    assert lo>0
    return lo

if __name__=='__main__':
    cmd,file,G=sys.argv[1:4]
    G=int(G)
    if cmd=='dual':
        dual(file,G,Q(sys.argv[4]) if len(sys.argv)>4 else None)
    else:
        p=readwin(file,G)
        print({k:float(v) for k,v in p.items()})
        print('A=4 quotient cap',float(capdec(p['U']/(p['F0']-4*p['J']),12)))
        if cmd=='ray': margin(p,Q(sys.argv[4]),Q(42))
        if cmd=='slab': margin(p,Q(sys.argv[4]),Q(sys.argv[5]),Q(sys.argv[6]),int(sys.argv[7]))
