"""Integer-interval Mertens certificate, Python 3.10; no floats or prime files."""
from math import factorial, isqrt
from bisect import bisect_left

B = 1 << 80
U = 10**6
N = 100_000_000
START = 10_000
P0 = 2_278_382
S0 = 2_278_383
V0 = 912_560
CUTS = sorted({P0,S0,V0,N})
W3 = [125000,130000,140000,150000,160000,180000,195000,220000,
      250000,300000,400000,500000,750000,1000000,1500000,2000000,3000000]
W2 = [135000,140000,150000,160000,180000,195000,200000,220000,
      250000,300000,400000,500000,750000,1000000,1500000,2000000,3000000]

def cd(x,y):
    assert y>0
    return -((-x)//y)

def lp(n,d,k):
    """Lower bound in B units for log(n/d), 1 <= n/d <= 2."""
    v=((n-d)*B)//(n+d)
    w=v*v//B
    acc=0
    for i in range(k):
        acc+=v//(2*i+1)
        v=v*w//B
    return 2*acc

L2 = lp(2,1,26)
TAB = [lp(j,256,26) for j in range(256,512)]

def lg(n,d=1):
    """Inclusive integer interval, in B units, for log(n/d), n,d>0."""
    assert n>0 and d>0
    if n<d:
        l,r=lg(d,n)
        return -r,-l
    h=n.bit_length()-d.bit_length()
    e=d<<h
    if e>n:
        h-=1
        e>>=1
    j=(n<<8)//e
    assert 256<=j<512
    l=h*L2+TAB[j-256]+lp(n<<8,e*j,5)
    return l,l+(h+1)*261+51

def ginterval():
    n=10_000
    hn=sum(B//k for k in range(1,n+1))
    l,r=lg(n)
    adj=B//(2*n) - B//(12*n*n) + B//(120*n**4)
    return hn-r-adj-2,hn+n-l-adj+2+cd(B,30*n**6)

GLO,GHI=ginterval()

def sieve(n):
    flag=bytearray(b'\1')*(n+1)
    flag[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if flag[p]:
            flag[p*p::p]=b'\0'*len(range(p*p,n+1,p))
    return flag

def add(state,p):
    sl,n,tl,th,vl,vh=state
    q=B//p
    if p<1024:
        l,r=lg(p,p-1)
        l-=q+1
        r-=q
    else:
        k=p*p
        l=0
        for j in range(2,7):
            l+=B//(j*k)
            k*=p
        r=l+5+cd(B,7*(k//p)*(p-1))
    a,b=lg(p)
    return (sl+q,n+1,tl+l,th+r,vl+a//p,vh+cd(b,p)),a//(p*(p-1)),cd(b,p*(p-1))

def lp_data(x,den=1):
    lo,hi=lg(x,den)
    lo2,_=lg(lo,B)
    _,hi2=lg(hi,B)
    return lo,hi,lo2,hi2

def residuals(A,Q,F,Z,constants):
    """Intervals for log product, reciprocal sum and log-weighted sum."""
    ml,mh,bl,bh=constants
    sa,na,ta,_,va,_=A
    sb,nb,_,tb,_,vb=Q
    return ((sa+ta-GHI-Z[3],sb+nb+tb-GLO-F[2]),
            (sa-mh-Z[3],sb+nb-ml-F[2]),
            (va+bl-Z[1],vb+bh-F[0]))

def coef(res,hi):
    # Scaled coefficient ceiling in U-units. For product exp(r)-1 <= r/(1-r).
    r,s,t=(max(abs(a),abs(b)) for a,b in res)
    assert r<B
    return (cd(U*r*hi**3,B**3*(B-r)),
            cd(U*s*hi**3,B**4),
            cd(U*t*hi**2,B**3))

def exact_product_ok(res,hi,c,unit):
    return max(map(abs,res)) <= lg(unit*hi**3+c*B**3,unit*hi**3)[0]

def exact_scaled_ok(x,state,constants,j,c,unit):
    F=lp_data(x)
    res=residuals(state,state,F,F,constants)[j]
    if j==0:
        return exact_product_ok(res,F[1],c,unit)
    return unit*max(map(abs,res))*F[1]**(3 if j==1 else 2)<=c*B**(4 if j==1 else 3)

def fixed_prime_guard(flag,a,b,A,constants,j,c,unit=U):
    """Endpoint certification on constant-prime-state pieces of [a,b]."""
    assert a>=START
    if not exact_scaled_ok(a,A,constants,j,c,unit):
        return False
    p=flag.find(b'\1',a+1,b+1)
    while p!=-1:
        if not exact_scaled_ok(p,A,constants,j,c,unit):
            return False
        A,_,_=add(A,p)
        if not exact_scaled_ok(p,A,constants,j,c,unit):
            return False
        p=flag.find(b'\1',p+1,b+1)
    return exact_scaled_ok(b,A,constants,j,c,unit)

def end_analysis(flag,tape,constants):
    tab=[W3,W3,W2]
    got=[[START]*len(W) for W in tab]
    a,A=tape[0]
    F=lp_data(a)
    fail=[0,0,0]
    stats=[0,0,0]
    goals=(1999990,1999990,2999995)
    baseline_onset=(P0,S0,V0)
    base_mx=[0,0,0]
    for b,Q in tape[1:]:
        Z=lp_data(b)
        ce=coef(residuals(A,Q,F,Z,constants),Z[1])
        for j in range(3):
            for i in range(bisect_left(tab[j],ce[j])):
                c=tab[j][i]
                # Refine only reasonably close cells; a failed guard may
                # conservatively move the onset later and never weakens proof.
                if ce[j]-c > 16000 or not fixed_prime_guard(flag,a,b,A,constants,j,c):
                    got[j][i]=b
            if a>=baseline_onset[j] and 10*ce[j]>goals[j]:
                stats[j]+=1
                if not fixed_prime_guard(flag,a,b,A,constants,j,goals[j],10*U):
                    fail[j]+=1
                    base_mx[j]=b
        a,A,F=b,Q,Z
    print("columns c (millionths), certified onset:", flush=True)
    for j in range(3):
        print(j,list(zip(tab[j],got[j])),flush=True)
        assert all(x<N for x in got[j])
    print("original-onset refinement cells:",stats, "failures:",fail,
          "last failed end:",base_mx,flush=True)
    return got,fail,base_mx

def root_proof(flag,st):
    """The exact sharp real onset for error 0.2/L^3 in product family."""
    assert not flag[P0]
    ql=st[0]+st[2]
    qh=st[0]+st[1]+st[3]
    r=P0*10**9
    l=(P0-1)*10**9
    d=10**9
    def which(x):
        flo,fhi,ll,lh=lp_data(x,d)
        zlo=ql-GHI-lh
        zhi=qh-GLO-ll
        assert 0<zlo<=zhi<B//100
        a,_=lg(5*fhi**3+B**3,5*fhi**3)
        _,b=lg(5*flo**3+B**3,5*flo**3)
        if zlo>b:
            return 1
        if zhi<a:
            return -1
        return 0
    assert which(l)==1 and which(r)==-1
    while r-l>1:
        mid=(l+r)//2
        w=which(mid)
        if w==0:
            break
        if w>0:
            l=mid
        else:
            r=mid
    assert r-l<=10
    print("sharp 0.2 product onset bracket /10^9:",l,r,flush=True)

def sum_roots(flag,tape,constants):
    d=10**4
    for end,j,target in [(S0,1,2),(V0,2,3)]:
        assert not flag[end]
        Q=next(st for x,st in tape if x==end)
        def w(x):
            F=lp_data(x,d)
            zlo,zhi=residuals(Q,Q,F,F,constants)[j]
            k=4-j
            assert zlo>0 and zhi<B//100
            if 10*zlo*F[0]**k>target*B**(k+1):
                return 1
            if 10*zhi*F[1]**k<target*B**(k+1):
                return -1
            return 0
        a,b=(end-1)*d,end*d
        assert w(a)==1 and w(b)==-1
        while b-a>1:
            m=(a+b)//2
            c=w(m)
            if c==0:
                if m>a+1 and w(m-1)==1: a=m-1
                if m<b-1 and w(m+1)==-1: b=m+1
                break
            if c>0: a=m
            else: b=m
        assert b-a<=3
        print("sharp sum onset (column, bracket /10^4):",j,a,b,flush=True)
    Q=next(st for x,st in tape if x==V0)
    F=lp_data(V0)
    z=residuals(Q,Q,F,F,constants)[2][0]
    assert z>0 and U*z*F[0]**2>299999*B**3  # earlier failed target is false

def main():
    flag=sieve(N)
    A=(0,0,0,0,0,0)
    tape=[]
    p=2
    lo=hi=0
    a=START
    rootst=None
    while True:
        while p>=0 and p<=a:
            A,l,r=add(A,p)
            lo+=l
            hi+=r
            p=flag.find(b'\1',p+1)
        tape.append((a,A))
        if a==P0:
            rootst=A
        if a==N:
            break
        a=min(a+max(1,a//25000),CUTS[bisect_left(CUTS,a+1)])
    assert rootst is not None and p==-1
    print("sieve primes:",A[1],"cells:",len(tape)-1,flush=True)
    assert tape[-1][0]==N
    # Uses proved uniform |theta(t)-t| <= t/5000 on t >= N.
    wl,wh=lg(N,N-1)
    pad=cd(cd(2*B,N-1)+wh,5000)
    bl,bh=GLO+lo+wl-pad,GHI+hi+wh+pad
    lnlo,lnhi=lg(N)
    curlo=curhi=0
    for j in range(13):
        jlo=(factorial(j)*B**(j+2))//(2*N*lnhi**(j+1))
        jhi=cd(factorial(j)*B**(j+2),2*N*lnlo**(j+1))
        if j%2:
            curlo-=jhi
            curhi-=jlo
        else:
            curlo+=jlo
            curhi+=jhi
        if j==11:
            il=curlo
    ih=curhi
    pad=cd(cd(B*B,N*lnlo)+ih,5000)
    ml=GLO-A[3]-ih-pad-cd(B,3*N*N)
    mh=GHI-A[2]-il+pad
    print("exact constants /2^80:", (GLO,GHI),(ml,mh),(bl,bh),flush=True)
    root_proof(flag,rootst)
    sum_roots(flag,tape,(ml,mh,bl,bh))
    got,fail,last=end_analysis(flag,tape,(ml,mh,bl,bh))
    assert got[0][W3.index(125000)]<=7_250_000
    assert got[1][W3.index(125000)]<=7_250_000
    assert got[2][W2.index(135000)]<=7_250_000
    assert fail==[0,0,0]

if __name__=='__main__':
    main()
