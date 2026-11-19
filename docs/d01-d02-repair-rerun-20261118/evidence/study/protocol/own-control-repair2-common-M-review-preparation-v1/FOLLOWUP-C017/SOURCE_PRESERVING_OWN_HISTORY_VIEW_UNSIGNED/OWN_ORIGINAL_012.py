from intervals import *
from math import isqrt
from hashlib import sha256
from array import array
from sys import argv
from math import factorial
LIMIT=int(argv[1]) if len(argv)>1 else 25*10**6
assert LIMIT>=10**7
# at 35 significant places, cumulative enclosures are still much
# tighter than the separately bounded normalization tails.
LO.prec=HI.prec=NE.prec=35
def sieve(n):
    s=bytearray(b'\x01')*(n+1)
    s[0:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if s[p]: s[p*p::p]=b'\x00'*((n-p*p)//p+1)
    return s

def constants(s):
    n=20000
    # Corrected composite trapezoid for f(t)=1/t.
    g=sum((I(1)/j for j in range(1,n+1)),I())-I(n).ln()-I(1)/(2*n)+I(1)/(12*n*n)-I(0,(1/(20*I(n-1)**4)).r)
    v,w=I(),I()
    Y=len(s)-1
    for p in range(2,len(s)):
        if not s[p]:continue
        pp=I(1)/p
        v+=-(1-pp).ln()-pp
        w+=I(p).ln()/(p*(p-1))
    # Main integral plus explicit theta-error tail (Dusart, eta_2=0.2).
    L=I(Y).ln()
    dt=I('.2')/L**2
    w0=-(1-I(1)/Y).ln()
    a=dt*(2/I(Y-1)+w0)
    # Dominant k=2 main integral, alternating with certified sign.
    def intpoly(k):
        return sum((I((-1)**j*factorial(j))/L**j for j in range(k+1)),I())/(2*Y*L)
    main=I(intpoly(15).l,(intpoly(14)/(1-I(1)/Y)).r)
    b=dt*(1/(Y-1)/L+main)
    return g,g-v-main+I(b.r.copy_negate(),b.r),g+w+w0+I(a.r.copy_negate(),a.r)

def loss(z):
    return maxi(z,-z)

if __name__=='__main__':
    s=sieve(LIMIT)
    print('sieve SHA256',sha256(s).hexdigest(),'count',sum(s),flush=True)
    gamma,M,B=constants(s)
    cg=gamma.exp()
    print('gamma',gamma,'M',M,'B3',B,flush=True)
    # Target constants (for normalized P,Q, sum 1/p, sum log(p)/p).
    targets=tuple(I(c) for c in ('.3','.2999996','.2999','.299','.295','.29','.285','.25','.22','.2','.19998','.19999','.1999','.199','.195','.19','.185','.18','.175','.17','.165','.16','.15','.14','.13','.12','.11','.1'))
    last_bad=[[0]*4 for _ in targets]
    maxima=[[D(0)]*4 for _ in range(12)]
    starts=(100000,500000,1000000,2000000,4000000,6000000,8000000,9000000,10000000,12000000,15000000,20000000)
    def check(x,L,LL,prod,a,b):
        if x<10000: return
        q=prod/(cg*L)
        sp=a-LL-M; sw=b-L+B
        # Endpoint monotonicity guards; see text. Check at both ends.
        assert q.l>D('.8') and q.r<D('1.3')
        assert sp.r<D('.1') and sw.r<D('1')
        v=[(loss(f)*L**k).r for f,k in ((1/q-1,3),(q-1,3),(sp,3),(sw,2))]
        for j in range(len(targets)):
            for i in range(4):
                if v[i]>=targets[j].l: last_bad[j][i]=x
        for j,start in enumerate(starts):
            if x>=start:
                maxima[j]=[max(c,d) for c,d in zip(maxima[j],v)]
    tests=sorted(D(x) for x in ('850000','900000','912559.998','912560','1000000','2278379.5','2278380','2278381','2278381.72','2278382','2278382.12','2278383','3461900','3462000','3500000','4000000','4994000','5000000','6000000','7000000','8000000','9000000','9999999','10000000','12000000','15000000','20000000','25000000') if D(x)<=LIMIT)
    def show(x,prod,a,b):
        L=I(x).ln()
        q=prod/(cg*L)
        v=[(loss(f)*L**k).r for f,k in ((1/q-1,3),(q-1,3),(a-L.ln()-M,3),(b-L+B,2))]
        print('threshold value',x,[HI.quantize(c,D('.000000001')) for c in v],flush=True)
    prod,a,b=I(1),I(),I()
    j=0
    for p in range(2,LIMIT+1):
        if not s[p]:continue
        while j<len(tests) and tests[j]<p:
            show(tests[j],prod,a,b);j+=1
        L=I(p).ln()
        if p>=10000: check(p,L,L.ln(),prod,a,b)
        prod*=I(p)/(p-1); a+=I(1)/p; b+=L/p
        if p>=10000: check(p,L,L.ln(),prod,a,b)
        while j<len(tests) and tests[j]==p:
            show(tests[j],prod,a,b);j+=1
    while j<len(tests):
        show(tests[j],prod,a,b);j+=1
    L=I(LIMIT).ln();check(LIMIT,L,L.ln(),prod,a,b)
    print('Last unproved endpoints (including one-sided prime limits)')
    for t,v in zip(targets,last_bad): print(t.l,v)
    print('Endpoint maxima rounded upward to 0.000001')
    for st,v in zip(starts,maxima): print(st,[HI.quantize(c,D('.000001')) for c in v])
