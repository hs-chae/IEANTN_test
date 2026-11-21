"""Exact numerical low-range Mertens audit, no assumed decimal constants."""
from bounds import I,F,exp,log,GAMMA,PI
from math import isqrt
C=F('1.00000075')

def primes_to(n):
    a=bytearray(b'\x01')*(n+1)
    a[0]=a[1]=0
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=bytes((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]]

def exact_constants(n):
    primes=primes_to(n)
    ta=I(0)
    tb=I(0)
    cached={}
    for p in primes:
        lp=log(p)
        cached[p]=lp
        ta+=lp/(p*(p-1))
        tb+=log(F(p,p-1))-F(1,p)
    ua=2*C*(1+F(1,n))/n
    ub=2*C/(n*log(n))
    e=-GAMMA-ta-I(0,ua)
    b=GAMMA-tb-I(0,ub.h)
    return e,b,cached

def absupper(v):return max(-v.l,v.h)

def run():
    E,B,logs=exact_constants(10000)
    EG=exp(GAMMA)
    for name,v in (('E',E),('B',B)):
        print(name,'interval in millionths:',(v.l*10**6).__floor__(),(v.h*10**6).__ceil__(),flush=True)
    A=I(0)
    bp=F(0)
    prod=F(1)
    worst={k:F(0) for k in range(4)}
    for m in range(2,300):
        if m in logs:
            A+=logs[m]/m
            bp+=F(1,m)
            prod*=F(m,m-1)
        if m<25: continue
        ends=[]
        for t in (m,m+1):
            ell=log(t)
            rr=prod/(EG*ell)
            es=[A-ell-E,bp-log(ell)-B,rr-1,1/rr-1]
            vals=[absupper(x) for x in es]
            z=3*ell*exp(-ell/2)/(8*PI)
            ends.append((vals,((z*ell).l,z.l,z.l,z.l)))
        for k in range(4):
            if k==0 and m<44: continue
            up=max(ends[0][0][k],ends[1][0][k])/min(ends[0][1][k],ends[1][1][k])
            u=F('.82') if m>=50 else (F(1) if k==0 else F('.985'))
            assert up<u, (m,k,float(up))
            if m>=50: worst[k]=max(worst[k],up)
    print('worst upper ratios on [50,300) in millionths:',
          [(v*10**6).__ceil__() for v in worst.values()])

if __name__=='__main__': run()
