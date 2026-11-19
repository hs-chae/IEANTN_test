"""Whole-ray power and logarithmic rows, plus exact clipping at small x."""
from smoothed import *
from mertens_new import simple_bound
from math import isqrt
a=I('1.048e-12')
def ac(t,b):
    t=I(t)
    j=(I('.0462')*exp(-(b-F(1,2))*t)+ I('3.1e-12')*exp(-(b-s0)*t)
       + minI(positive_sum(coeff(b),t,b),positive_sum(co_old(b),t,b))/H
       +I('1.84')*exp(-b*t))
    return j
def extra(t,b):
    t=I(t)
    return (1+1/t)*ac(t,b)+I('1.092')*exp(-(b-F(1,2))*t)
def cs(t,b): return minI(oldC(t,b),C(t,b))
def norm(t,b): return cs(t,b)+extra(t,b)
def h_at(t,b,y,hy):
    return I(hy)*exp(-(1-b)*(I(t)-I(y))/2)
def smbody(t,b,y,hy):
    t=I(t); h=h_at(t,b,y,hy)
    return h/2+I('117.02')*exp(-t/2)+2*kernel(t.a,t.b,b)/h+I('1.84')*exp(-t)
def smooth_norm(t,b,y,hy):
    t=I(t)
    # frozen e^hy and 1+1/y; one valid convex majorant uses *either*
    # choice of density coefficient globally, here use coeff(b).
    j=(I('.0462')*exp(-(b-F(1,2))*t)+ I('3.1e-12')*exp(-(b-s0)*t)
       + positive_sum(coeff(b),t,b)/H +I('1.84')*exp(-b*t))
    return exp(I(hy))*smbody(t,b,y,hy)*exp((1-b)*t)+(1+1/I(y))*j+I('1.092')*exp(-(b-F(1,2))*t)

def constants():
    # Own D01 floor validates these constants; do not import a full-RH premise.
    from D01_check import S
    G=I(0)
    N=2**19
    g=sum((S//i for i in range(1,N+1)))
    # Convex trapezoid error: 0 <= gamma-(H_N-log N-1/(2N)) <= 1/(8N^2).
    gl=I(g,g+N)-log(N)-I(F(1,2*N))
    G=gl+rng(0,F(1,8*N*N))
    M=rng('.261497212838','.261497212858')
    B3=rng('1.332582275723','1.332582275744')
    return G,M,B3

def finite(L,b,cap,modes=(0,1,2,3)):
    G,M,B3=constants()
    p=[u for u in range(2,10010) if all(u%i for i in range(2,isqrt(u)+1))]
    q=u=j=I(0); best=[0]*4; count=0
    for l,r in zip(p,p[1:]):
        q+=log(F(l,l-1)); u+=I(F(1,l)); j+=log(l)/l
        if r<=L or l>10000: continue
        def bound(L,R):
            t=log(rng(L,R))
            d=q-log(t)-G
            jj=j+B3-t
            uu=u-log(t)-M
            e=exp((1-b)*t)
            return [(exp(d)-1)*t*e,(exp(-d)-1)*t*e,uu*t*e,jj*e]
        def cover(L,R):
            nonlocal count
            upper=[max(abs(z.a),abs(z.b)) for z in bound(L,R)]
            if any(upper[i]>=I(cap).a for i in modes):
                if R-L<=F(1,1024):
                    lo=bound(L,L)
                    print('uncertified segment',L,R,
                          [approx(a) for a in lo],flush=True)
                    raise ValueError('finite target not certified')
                mid=F(L+R)/2
                cover(L,mid); cover(mid,R)
                return
            for i,z in enumerate(upper):
                best[i]=max(best[i],z)
            count+=1
        cover(max(l,L),min(r,10000))
    vals=[I(v,v) for v in best]
    for i in modes: less(vals[i],cap)
    print('finite closed log-gap cells',L,b,cap,modes,count,[approx(v)[1] for v in vals],flush=True)
def checks():
    less(log(I(H)/(2*PI))**2/I('6.28')+I('1.8642'),'117.02')
    w=log(10**8); u=log(10**13)
    for b,lo,y,z,h,cap in [(J,10000,'166.41','169.4','1.05e-12','.25665'),(Q,560000,'185.14','186.8','1.05e-12','.01322')]:
        y,z=I(y),I(z)
        def mid(t):
            # For this full convex segment use the old J_b, no switching.
            t=I(t); k=1-b
            return a*exp(k*t)+I('114.762')*exp(-(b-F(1,2))*t)+(1+1/u)*(I('.0462')*exp(-(b-F(1,2))*t)+I('3.1e-12')+I('1.84')*exp(-b*t))
        rows=[(I('1.88')*exp(-(b-F(1,2))*log(lo)),log(lo)),
              (I('1.94')*exp(-(b-F(1,2))*w), w),
              (mid(u),u),(mid(y),u),(smooth_norm(y,b,y,h),y),
              (smooth_norm(z,b,y,h),y),(norm(z,b),z)]
        print('middle trial',b,[approx(rel(m,t,b))[1] for m,t in rows],flush=True)
        for m,t in rows: less(rel(m,t,b),cap)
        print('whole closed power ray',b,lo,cap,flush=True)
    for b,n,cap in [(J,170,'.2557'),(J,180,'.2402'),(J,186,'.2325'),
                    (J,200,'.21771'),(J,250,'.18611'),(J,300,'.16962'),
                    (J,500,'.14409'),(J,1000,'.12952'),(J,2300,'.12258'),
                    (Q,200,'.012400'),(Q,300,'.009683'),(Q,1000,'.007418'),(Q,2300,'.007024')]:
        t=I(n); less(rel(norm(t,b),t,b),cap)
        print('spectral closed ray',b,n,cap,flush=True)
    for b,n,cap in [(Q,10**6,'.006665'),(J,50_000,'.1166'),(J,10**6,'.11627')]:
        t=I(n)
        less(rel(simple_bound(t,b)+extra(t,b),t,b),cap)
        print('continuous closed ray',b,n,cap,flush=True)

def logchecks():
    # Through 57 use finite RH. Up to y use CH2 plus the signed integral tail.
    # After y use the decreasing smoothed logarithmic majorant.
    for b,ys,hh,cap in [(J,'166.41','1.05e-12','2.903e-8'),(Q,'185.14','1.05e-12','3.595e-8')]:
        y=I(ys); k=1-b
        def trans(n,d): return n/(1-n/d**3)
        def old_extra(t):
            return (I('1.092')+I('.0462')*(1+1/t))*t*t*exp(-t/2)+(1+1/t)*(I('3.1e-12')*t*t*exp(-k*t)+I('1.84')*t*t*exp(-t))
        for t,m in [(I(61),cap)]:
            # t^2 e^(-r t) decreasing for r>=k and t>=65.
            z=[a*v*v+I('113.67')*v*v*exp(-v/2)+old_extra(v) for v in [t,y]]
            v = y*y*exp(-k*y)*smooth_norm(y,b,y,hh)
            print('log trial',b,approx(t)[0],[approx(k)[1] for k in z],approx(v)[1],m,flush=True)
            for e in z+[v]:
                less(trans(e,t),m)
            print('log closed ray',b,approx(t)[0],m,flush=True)
        for n,m in ([(170,'2.18e-8'),(180,'4.76e-9'),(185,'2.24e-9'),(200,'2.34e-10'),(250,'1.27e-13')] if b==J else [(200,'6.90e-9'),(250,'1.78e-11')]):
            t=I(n); v=t*t*exp(-k*t)*norm(t,b)
            less(trans(v,t),m)
            print('scaled logarithmic closed ray',b,n,m,flush=True)

if __name__=='__main__':
    import sys
    cmd=sys.argv[1]
    if cmd=='analytic': checks()
    if cmd=='log': logchecks()
    if cmd=='finite': finite(F(sys.argv[2]),J,sys.argv[3],(0,1,2) if len(sys.argv)>4 else (0,1,2,3))


    if cmd=='weighted-root':
        b=J
        ss=sum((log(p)/p for p in range(2,284) if all(p%d for d in range(2,isqrt(p)+1))),I(0))
        j=ss+rng('1.332582275723','1.332582275744')
        def f(x):
            t=log(I(x))
            return (j-t)*exp((1-b)*t)
        for n in range(284,286):
            assert any(n%d==0 for d in range(2,isqrt(n)+1))
        def bracket(l,r):
            less('.25665',f(l)); less(f(r),'.25665')
            print('weighted exact root bracket',l,r,flush=True)
        bracket('284.690','284.691')
        from fractions import Fraction
        l,r=F('284.690'),F('284.691')
        while r-l>F(1,10**7):
            m=(l+r)/2
            if f(m).a>I('.25665').b: l=m
            elif f(m).b<I('.25665').a: r=m
            else: break
        bracket(l,r)
        less(0,j-log(285)); less((1-b)*(j-log(283)),1)

    if cmd=='three-roots':
        G,M,_=constants()
        primes=[x for x in range(2,120) if all(x%i for i in range(2,isqrt(x)+1))]
        assert primes[-1]==113
        A=exp(sum(log(F(p,p-1)) for p in primes)-G)
        U=sum(I(F(1,p)) for p in primes)-M
        k=1-J
        lo,hi=log(117),log(119)
        less(hi,A)
        less(log(hi),U)
        less(k*(A-lo),1)
        less((k*hi+2)*(1-lo/A),1)
        less((k*hi+1)*(U-log(lo)),1)
        def f(x,mode):
            t=log(I(x)); e=exp(k*t)
            if mode==0: return e*(A-t)
            if mode==1: return e*t*(1-t/A)
            return e*t*(U-log(t))
        for i in range(3):
            l,r=F(117),F(119)
            less('.25665',f(l,i)); less(f(r,i),'.25665')
            while r-l>F(1,10**7):
                m=(l+r)/2
                if f(m,i).a>I('.25665').b: l=m
                elif f(m,i).b<I('.25665').a: r=m
                else: break
            less('.25665',f(l,i)); less(f(r,i),'.25665')
            print('exact root bracket',i,l,r,float(l),float(r),flush=True)
