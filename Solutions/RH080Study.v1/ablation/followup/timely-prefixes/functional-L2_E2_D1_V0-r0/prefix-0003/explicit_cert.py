#!/usr/bin/python3.10
"""Rational constants for the explicit Blanquer--Robles / smaller-block variant."""
import sys,json
from fractions import Fraction as Q
from math import isqrt,factorial
from pathlib import Path
from window_cert import PI,fft,primal,positive_area,decimals

def loclog(x):
    assert 1<=x<=2
    u=(x-1)/(x+1)
    n=45
    v=2*sum(u**(2*k+1)/(2*k+1) for k in range(n))
    return v,v+2*u**(2*n+1)/((2*n+1)*(1-u*u))

def logb(x):
    assert x>=1
    r=Q(x);b=0
    while r>=2:r/=2;b+=1
    a,c=loclog(r)
    l,h=loclog(Q(2))
    return a+b*l,c+b*h

def rounding(x,scale=10**18):
    return (x*scale).__ceil__()

def logmoment(a,m,scale,L=2**14):
    n=len(a)-1
    inp=[int(x*scale) for x in a[:-1]]+[0]*(L-2*n+1)+[int(x*scale) for x in reversed(a[1:-1])]
    assert len(inp)==L
    re,_,err=fft(inp,L)
    U,_,de=fft([0,10**25],L)
    h=Q(m,L)
    def sample(k):
        par=Q(k,L)
        uk=k%L
        eps=(1-Q(U[uk]-de,10**25))/2
        return eps*(abs(re[uk])+err)/(scale*m*(PI*par)**2)
    start=L//m
    stop=2*L
    assert stop*h==160 and start*h>=Q(99,100)
    amp=sample(start)
    raw=0
    for k in range(start,stop):
        aa=h*k
        bb=h*(k+1)
        bamp=sample(k+1)
        if bb<=1:
            logupper=Q(0)
        else:
            j=0
            while 2**j<bb:j+=1
            logupper=Q(694,1000)*j
        errc=133*h*h/(8*aa*aa)
        raw += rounding(2*h*((amp+bamp)/2+errc)*logupper)
        amp=bamp
    return Q(raw,10**18)+Q(207,1000)*(1+logb(Q(160))[1])/160

def prime(n):return n>=2 and all(n%k for k in range(2,isqrt(n)+1))
def finite(c):
    for x in range(4,1424):
        p=x+1
        while not prime(p):p+=1
        # x real need only plain integer floors here; right window endpoint increasing.
        assert c*c*x*logb(Q(x))[0]**2>(p-x)**2, (x,p)
    print('Exact finite checks, real floor cells from x=4 through x=1423, coefficient',c)

if __name__=='__main__':
    p=Path(sys.argv[1])
    X=json.loads(p.read_text()); m=X['m']; scale=X['scale']
    a=[Q(j,scale) for j in X['coefficients']]+[Q(0)]
    J=2*sum(positive_area(v,w) for v,w in zip(a[m:],a[m+1:]))/m
    v=(2*sum(a)-a[0])/m
    U=Q('0.781771946951');D=Q('0.918513815592')
    if len(sys.argv)>2 and sys.argv[2]=='fft':
        u,j,b=primal(str(p),2**20,Q(4),Q('.851127043'))
        assert u<=U and j==J and b==v
    assert v-4*J>D and J<Q('.020372') and v< Q('1.000001')
    H=max(0,a[m])+sum(max(0,max(0,b)-max(0,c)) for c,b in zip(a[m:],a[m+1:]))
    A0=(2*sum(map(abs,a))-abs(a[0]))/m
    V0=2*sum(abs(b-c) for c,b in zip(a,a[1:]))
    sl=[m*(b-c) for c,b in zip(a,a[1:])]
    V1=2*(abs(sl[0])+sum(abs(b-c) for c,b in zip(sl,sl[1:]))+abs(sl[-1]))
    assert H<Q('.114278') and A0<Q('1.004') and V0<Q('1.405') and V1<Q('4.062')
    assert max(map(abs,a))<Q('.7')
    assert 25*V1+20*V0+2*A0<133 and V1/(2*PI**2)<Q('.207')
    assert (5*V1+2*V0)/(2*PI)<4 and Q(10)*Q(22,7)*A0+4<36
    assert 2*sum(a)/m>0
    moment=logmoment(a,m,scale)
    print('Log moment upper, scaled by 1e12:',decimals(moment,12)[1],flush=True)
    assert moment<Q('.025')
    assert 4*(Q('4.606')+Q('.001'))/(1-Q('4.606')/40)<Q('20.83')
    assert Q('20.83')*Q('.500001')<Q('10.416')
    assert sum(Q(20**k,factorial(k)) for k in range(34))>4*10**8
    assert logb(Q(2))[0]>Q('.69') and logb(Q(2))[1]<Q('.694')
    assert logb(Q(10))[1]<Q('2.303')
    assert logb(Q(1423))[0]>7
    assert logb(Q(10**18))[0]>40
    assert Q(41**2*121,4*10**8)<Q('.001')
    assert Q('.025')+Q('.0001')+Q('.001')+Q('.000003')<Q('.02611')
    c=Q('.851127043')
    assert c*D>U
    def margin(c,t):
        K=Q('.02611')+Q('.905')*Q('.114278')+Q('10.416')*c*Q('.020372')
        return (c*D-U)*t/2+U*logb(c*t/2)[0]-K
    for c,t in [(Q('.851127043'),40),(Q('.799999'),40),(Q('.799999'),114),(Q('.779999'),40),(Q('.779999'),70),(Q('.776999'),40),(Q('.776999'),65)]:
        s=margin(c,t)
        print('c,t,margin lower scaled 1e12',c,t,decimals(s,12)[0],flush=True)
        assert s>0
    finite(Q('.776999'))
