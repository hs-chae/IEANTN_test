"""Exact finite bridge below 369; no floating point; not source-first PV."""
from math import isqrt

D, SCALE, TERMS = 100, 10**15, 10

def sieve(limit):
    a = bytearray([1])*(limit+1)
    a[:2] = bytes(2)
    for p in range(2, isqrt(limit)+1):
        if a[p]:
            a[p*p::p] = bytes(1+(limit-p*p)//p)
    return a

def log_bounds_unit(v,w):
    # Scaled lower and upper bounds, using log(v/w)=2*atanh((v-w)/(v+w)).
    assert 0 < w <= v <= 2*w
    if v==w:
        return 0,0
    p,q = v-w,v+w
    pp,qq=p,q
    lo=0
    for k in range(TERMS):
        lo+=(2*SCALE*pp)//((2*k+1)*qq)
        pp*=p*p
        qq*=q*q
    u,t=2*SCALE*pp*q*q,(2*TERMS+1)*qq*(q*q-p*p)
    return lo, lo+TERMS+(u+t-1)//t

LOW2,HIGH2=log_bounds_unit(2,1)
def log_bounds(v,w):
    assert v>=w>0
    a=0
    while v>=2*w:
        w*=2
        a+=1
    lo,hi=log_bounds_unit(v,w)
    return a*LOW2+lo,a*HIGH2+hi

def bounds(m,d):
    # Integer endpoints inclusive of the common strict-open inner interval
    # for all n in the closed real cell [m/d,(m+1)/d].
    return (m+1)**3//d**3+1, ((m+d)**3-1)//d**3

def check(a,first,last,cn,cd,d=D):
    assert 2*d<=first<last and d>1
    left,right=bounds(first,d)
    assert right<len(a)
    count=a.count(1,left,right+1)
    minimum=10**7
    worst=None
    for m in range(first,last):
        l,r=bounds(m,d)
        assert left<=l<=right+1 and right<=r<len(a)
        count+=a.count(1,right+1,r+1)-a.count(1,left,l)
        left,right=l,r
        lo,_=log_bounds(m,d)
        v,w=count*lo*d*d,SCALE*(m+1)**2
        if v*cd<=cn*w:
            raise ValueError((m,d,count,cn,cd,v,w))
        mil=v*10**6//w
        if mil<minimum:
            minimum,worst=mil,m
    return (first,last,d,cn,cd,minimum,worst)

def failing_point(a,m,d,cn,cd):
    left=m**3//d**3+1
    right=((m+d)**3-1)//d**3
    assert right<len(a)
    count=a.count(1,left,right+1)
    _,hi=log_bounds(m,d)
    assert cd*count*hi*d*d<=cn*SCALE*m*m
    return (m,d,count,cn,cd)

def selftest():
    for p,flag in enumerate(sieve(10000)):
        assert flag == (p>=2 and all(p%k!=0 for k in range(2,isqrt(p)+1)))
    assert bounds(200,100)==(9,26)
    assert log_bounds(1,1)[0]==0
    assert log_bounds(2,1)==(LOW2,HIGH2)
    assert 693147180540000 < LOW2 <= HIGH2 < 693147180562000
    # Verify moving counts on a small nontrivial exact interval by direct counts.
    a=sieve(1000)
    left,right=bounds(200,100)
    ct=a.count(1,left,right+1)
    for m in range(200,700):
        l,r=bounds(m,100)
        ct+=a.count(1,right+1,r+1)-a.count(1,left,l)
        assert ct==a.count(1,l,r+1)
        left,right=l,r

def main():
    selftest()
    a=sieve(370**3)
    for start,c,d in [(2,84,100),(12,94,100),(25,96,100),(77,96699,100000)]:
        print("finite strict coverage",check(a,start*D,369*D,c,d),flush=True)
    print("finite strict coverage",check(a,218069,230000,96699,100000,10000))
    print("finite strict coverage",check(a,23000,77000,96699,100000,1000))
    print("finite-point obstruction",failing_point(a,218068,10000,96699,100000))
    lo,hi,d=218068,218069,10000
    p=11863
    assert (lo+d)**3<p*d**3<(hi+d)**3
    assert 10369*d**3<lo**3 and hi**3<10371*d**3
    assert a[p] and not a[10370] and a.count(1,10371,11863)==149
    L,_=log_bounds(lo,d)
    assert 150*L*d*d*100000>96699*SCALE*hi**2
    _,U=log_bounds(hi,d)
    assert 149*U*d*d*100000<=96699*SCALE*lo**2
    print("sharp algebraic onset 11863^(1/3)-1, strictly excluded",flush=True)

if __name__=="__main__":
    main()
