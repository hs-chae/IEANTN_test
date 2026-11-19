#!/usr/bin/python3.10
"""Exact sieve, fixed-point arithmetic, real-cell Mertens bounds, independent of added psi input."""
from bounds import I,Q,F,C,N,LN2,assertlt
from math import isqrt
from bisect import bisect_right

S=1<<80
# The last cell ends beyond exp(17.8) (join to bounds.py).
LIMIT=54000000
START=500000
DEN=80000
def floor(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def ceil(x): return int(x.to_integral_value(rounding='ROUND_CEILING'))
def snap(x):
    x=S*x
    return floor(x.l),ceil(x.r)
def fixed(l,r):return I(l,r)/S
def gamma():
    n=200000
    w=sum(S//i for i in range(1,n+1))
    g=fixed(w,w+n)-I(n).ln()-I(1)/(2*n)
    return I(g.l,(g+I(1)/(n*n)).r)

def sieve(n):
    b=bytearray(b'\x01')*(n+1); b[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if b[p]:
            b[p*p::p]=b'\x00'*((n-p*p)//p+1)
    p=2
    while p!=-1:
        yield p
        p=b.find(b'\x01',p+1)

def run():
    assertlt(I('17.8').exp(),LIMIT)
    log2lo,log2hi=snap(LN2)
    logs=[snap((I(j)/4096).ln()) for j in range(4096,8192)]
    g=gamma()
    gs=snap(g)
    Mlo,Mhi=0,0
    Blo,Bhi=0,0
    plo=phi=slo=shi=tlo=thi=0
    L=[]
    critical={}
    after={912559:912560,2278379:2278383}
    n=START
    checkpoints=[]
    while n<LIMIT:
        checkpoints.append(n);n+=n//DEN
    checkpoints.append(LIMIT)
    t=iter(checkpoints)
    n=next(t)
    for p in sieve(LIMIT):
        while p>n:
            L.append((n,plo,phi,slo,shi,tlo,thi));n=next(t)
        # k*log(2)+log(j/4096)+log(1+r)
        k=p.bit_length()-1; j=(4096*p)>>k; d=j<<k; z=4096*p-d
        lower,upper=logs[j-4096]
        v=S*z//d; z2=z*z; d2=d*d
        w=S*z2//(2*d2); u=S*z2*z//(3*d2*d)
        # Alternating series, first omitted term <= 2^-50.
        lp=k*log2lo+lower+v-w+u-1-(S>>50)
        hp=k*log2hi+upper+v-w+u+2
        quot=S//p
        slo+=quot;shi+=quot+1
        tlo+=lp//p;thi+=hp//p+1
        if p<=1024:
            al,au=snap(-(1-I(1)/p).ln()-I(1)/p)
        else:
            p2=p*p;p3=p2*p;p4=p3*p;p5=p4*p;p6=p5*p
            al=S//(2*p2)+S//(3*p3)+S//(4*p4)+S//(5*p5)
            au=al+5+2*S//p6
        Mlo+=al;Mhi+=au
        plo+=quot+al;phi+=quot+au+1
        Blo+=lp//(p*(p-1));Bhi+=hp//(p*(p-1))+1
        if p in after:
            critical[p]=(fixed(plo,phi),fixed(slo,shi),fixed(tlo,thi))
        assert all(not a<p<=b for a,b in after.items())
    L.append((LIMIT,plo,phi,slo,shi,tlo,thi))
    assert len(L)==len(checkpoints)
    l=I(LIMIT).ln()
    delta=Q('.2')/l**2
    k=I(1)/(2*LIMIT)/l
    v=I(1);poly=I(1);even=None
    for n in range(1,10):
        v=-v*n/l;poly+=v
        if n==8:even=poly
    rad=k*delta*(3+1/l)
    mtail=I((k*poly-rad).l,(k*even+rad+I(1)/(LIMIT**2)).r)
    w=-(1-I(1)/LIMIT).ln()
    rad=delta*(2/I(LIMIT-1)+w)
    btail=w+I(rad.r.copy_negate(),rad.r)
    M=g-fixed(Mlo,Mhi)-mtail
    B=g+fixed(Blo,Bhi)+btail
    print('finite constants',M,B,g,flush=True)
    # Local exact earlier real thresholds for the original coefficients.
    for k,p,l,r,t in [
        (0,2278379,'2.710','2.713','.2'),
        (1,2278379,'2.574','2.577','.2'),
        (2,2278379,'3.111','3.115','.2'),
        (3,912559,'.997','.998','.3'),
    ]:
        pr,sr,wr=critical[p];tt=I(t)
        upr=I(after[p]);lpr=I(p)
        def errors(L):
            zz=pr-g-L.ln()
            return zz.exp()-1,1-(-zz).exp(),sr-M-L.ln(),wr+B-L
        span=I(lpr.ln().l,upr.ln().r)
        y=errors(span)[k]
        assertlt(0,y)
        assertlt(y,Q('.01'))
        def metric(x):
            z=I(p)+I(x);L=z.ln()
            return errors(L)[k]*L**(2 if k==3 else 3)
        assertlt(tt,metric(l));assertlt(metric(r),tt)
        print('local threshold',k,p,l,r,metric(l),metric(r),flush=True)
    targets={Q(c):[0,0,0] for c in ['.3','.25','.2','.18','.15','.12','.1']}
    a=L[0];A=I(a[0]).ln()
    for b in L[1:]:
        Bx=I(b[0]).ln()
        log=I(A.l,Bx.r)
        llog=log.ln()
        z=fixed(a[1],b[2])-g-llog
        # Both logarithms of normalized products lie in +/- absz.
        absz=max(z.l.copy_negate(),z.r)
        y=fixed(a[3],b[4])-M-llog
        w=fixed(a[5],b[6])-log+B
        ms=[(I(absz)/(1-I(absz))*I(Bx.r)**3).r,
            (I(max(y.l.copy_negate(),y.r))*I(Bx.r)**3).r,
            (I(max(w.l.copy_negate(),w.r))*I(Bx.r)**2).r]
        for q in targets:
            for j,m in enumerate(ms):
                if m>=q: targets[q][j]=b[0]
        a=b;A=Bx
    print('whole-cell safe onsets',targets,'(0 means no failure on checked range)',flush=True)
    for c,dom in [('.3',[625000,625000,912600]),('.25',[1515000,1515000,1521000]),
                  ('.2',[3446000,3446000,3458000]),('.18',[3460000,3460000,3471000]),
                  ('.15',[5385000,5385000,7117000]),('.12',[12874000,12874000,12895000]),
                  ('.1',[12922000,12922000,18338000])]:
        assert all(u<=v for u,v in zip(targets[Q(c)],dom)),(c,dom,targets[Q(c)])
if __name__=='__main__':run()
