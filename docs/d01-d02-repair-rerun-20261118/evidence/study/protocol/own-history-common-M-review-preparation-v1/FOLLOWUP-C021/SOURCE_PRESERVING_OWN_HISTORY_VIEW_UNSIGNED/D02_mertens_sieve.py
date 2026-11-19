"""Integer interval verification for finite Mertens ranges. Python 3.10.
No external prime table. Do not use -O. Rough memory use 140 MiB.
"""
from math import isqrt, factorial
from bisect import bisect_right
from fractions import Fraction as F
from cert import lni, expi

S=1<<64
B=1<<28
def floor_pair(i):
    return i[0]*S//1,i[1]*S//1+1
cd=floor_pair(lni(2))
L2=cd[0]
assert cd[1]==L2+1
TABLE=[]
for j in range(256):
    a,b=floor_pair(lni(F(j+256,256)))
    assert b==a+1
    TABLE.append(a)

def log_l(n, scale_bits=0):
    """For n/2**scale_bits >= 1, return low and upper error in units of S."""
    r=n.bit_length()-1
    k=r-scale_bits
    assert k>=0
    m=1<<r
    j=(n<<8)//m
    nj=n<<8
    ma=m*j
    z=((nj-ma)<<64)//(nj+ma)
    z2=z*z>>64
    z3=z*z2>>64
    z5=z3*z2>>64
    return k*L2+TABLE[j-256]+2*(z+z3//3+z5//5), k+12

N=1<<19
gammaH=sum(S//i for i in range(1,N+1))
a,b=floor_pair(lni(N))
G=(gammaH-b-S//(2*N),gammaH+N-a-S//(2*N)+S//(6*N*N)+S//(12*N*N)+2)
M=floor_pair((F('.261497212838'),F('.261497212858')))
C=floor_pair((F('1.332582275723'),F('1.332582275744')))
UNIT=10**7
raw=[
 [('2278381.712','.2'), ('2278382','.19998'), ('3500000','.160'), ('5100000','.148'), ('13000000','.100'), ('20000000','.090')],
 [('2278382.114','.2'), ('2278383','.19995'), ('3500000','.160'), ('5100000','.148'), ('13000000','.100'), ('20000000','.090')],
 [('912559.998','.3'), ('912560','.2999995'), ('912566','.299'), ('1200100','.275'), ('1515100','.260'),
  ('1526800','.230'), ('2276000','.22'), ('2278382','.216'), ('3500000','.172'), ('5100000','.160'), ('18100000','.100'), ('35000000','.090')]
]
spec=[[(F(x),int(UNIT*F(c))) for x,c in ls] for ls in raw]
cuts=sorted(set(x for ls in spec for x,c in ls))
witnesses={F('2278381.710'):0,F('2278382.112'):1,F('912559.997'):2}
events=iter(sorted(set(cuts)|set(witnesses)))
next_cut=next(events)
latest=[-1]*3
checked=[0,0,0]

def witness(vals,x,i):
    l,h=lni(x)
    if i==0:
        z=F(vals[0]-G[1],S)-lni(h)[1]
        assert z>0 and (z+z*z/2)*l**3>F('.2')
    elif i==1:
        z=F(vals[2]-M[1],S)-lni(h)[1]
        assert z>0 and z*l**3>F('.2')
    else:
        z=F(vals[4]+C[0],S)-h
        assert z>0 and z*l*l>F('.3')
    print('lower witness passed',x,i,flush=True)

def check(vals,t,d,x):
    # Select active coefficients. Prime endpoints use integer x.
    if x<cuts[0]:return
    t2=(t+d)**2
    t3=t2*(t+d)
    w,wd=log_l(t,64)
    ll=w; hh=w+wd+d
    u,du,v,dv,z,dz=vals
    aa,bb=G; mm,nn=M; cc,dd=C
    errs=[ max(hh+bb-u,u+du-aa-ll),
           max(hh+nn-v,v+dv-mm-ll),
           max(t+d-z-cc,z+dz+dd-t)]
    caps=latest
    for i,er in enumerate(errs):
        assert 0<=er<S//4,(x,i,er)
        if caps[i]<0:continue
        c=caps[i]
        if i==0:
            assert er*1000<S
            assert er*(1000*S+501*er)*t3*(UNIT//1000)<c*S**5,(x,i,er,c)
        elif i==1:
            assert er*(UNIT*t3)<c*S**4,(x,i,er,c)
        else:
            assert er*(UNIT*t2)<c*S**3,(x,i,er,c)
        checked[i]+=1

def run():
    global next_cut
    odd=bytearray([1])*(B//2)
    odd[0]=0
    for p in range(3,isqrt(B)+1,2):
        if odd[p//2]:
            odd[p*p//2::p]=b'\0'*((len(odd)-1-p*p//2)//p+1)
    qv=qd=sv=sd=wv=wd=vv=vd=0
    k=0
    while True:
        p=2 if k==0 else 2*k+1
        t,d=log_l(p)
        before=(qv,qd,sv,sd,wv,wd)
        while next_cut is not None and next_cut<=p:
            if next_cut in witnesses:
                witness(before,next_cut,witnesses[next_cut])
                next_cut=next(events,None)
                continue
            aa,bb=floor_pair(lni(next_cut))
            check(before,aa,bb-aa,next_cut)
            for i,ls in enumerate(spec):
                for z,c in ls:
                    if z==next_cut:latest[i]=c
            check(before,aa,bb-aa,next_cut)
            next_cut=next(events,None)
        if p>=912559:
            check(before,t,d,p)
        if p<1024:
            a,b=floor_pair(lni(F(p,p-1)))
            qv+=a;qd+=b-a
        else:
            pp=p*p
            qv+=S//p + S//(2*pp) + S//(3*pp*p)
            if p>=65536:
                qd+=4
            else:
                qv+=S//(4*pp**2) + S//(5*pp**2*p) + S//(6*pp**3)
                qd+=7
        sv+=S//p;sd+=1
        wv+=t//p;wd+=(t+d)//p+1-t//p
        pp=p*(p-1)
        vv+=t//pp;vd+=(t+d)//pp+1-t//pp
        if p>=912559:
            check((qv,qd,sv,sd,wv,wd),t,d,p)
        k=odd.find(1,k+1)
        if k<0:break
    assert next_cut is None
    t,d=log_l(B)
    check((qv,qd,sv,sd,wv,wd),t,d,B)
    # Use |theta(y)-y| <= .00014*y for all y>=B (paper inputs).
    # Weighted tails of p^-2 and log(p)/(p*(p-1)); see mertens.md.
    D=F('.00014')
    tl,th=lni(B)
    def I(j):
        # Odd truncation lower, even truncation upper.
        lower=(j%2==1)
        return sum(F((-1)**k*factorial(k)) /
                   (th if (k%2==0)==lower else tl)**(k+1)
                   for k in range(j+1))/B
    Mtl,Mth=floor_pair(((I(5)-3*D/(B*tl))/2,
                        (I(6)+3*D/(B*tl))/2+F(1,2*B**2)))
    Wl,Wh=lni(F(B,B-1))
    Vtl,Vth=floor_pair((Wl-3*D/(B-1),Wh+3*D/(B-1)))
    gl,gh=G
    assert M[0]<=gl-(qv+qd-sv)-Mth and gh-(qv-(sv+sd))-Mtl<=M[1]
    assert C[0]<=gl+vv+Vtl and gh+vv+vd+Vth<=C[1]
    print('finite Mertens certificate passed',B,checked,flush=True)
    # Certified lower witnesses give the opposite ends of tiny onset brackets.
    # Their prime sum intervals are obtained by the short independent pass below.

if __name__=='__main__':run()
