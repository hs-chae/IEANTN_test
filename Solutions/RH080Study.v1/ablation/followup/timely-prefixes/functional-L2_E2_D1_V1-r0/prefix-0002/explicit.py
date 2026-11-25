#!/usr/bin/python3.10
"""Effective RH bound via an A=4 window; exact rational scalar checks."""
from check import Q,need,read,primal,up,PL,PU
from pathlib import Path
from math import isqrt
import argparse

def pos(x):return max(0,x)
def pairs(a):return zip(a,a[1:])
def lexp(x,n=36):
    t=s=Q(1)
    for i in range(1,n+1):
        t*=x/i;s+=t
    return s
def uexp(x,n=200):
    need(0<=x<n+2,"exponential geometric tail")
    t=s=Q(1)
    for i in range(1,n+1):
        t*=x/i;s+=t
    return s+t*x/(n+1)/(1-x/(n+2))
def loglo(y,n=50):
    # y>=1, log y = 2 atanh((y-1)/(y+1)), all summands nonnegative.
    need(y>=1,"log lower requires y>=1")
    v=Q(y-1,y+1)
    return 2*sum(v**(2*j+1)/(2*j+1) for j in range(n))
def sqrtlo(x,d=10**8):return Q(isqrt(x*d*d),d)

def explicit(m,a,C,L):
    need(len(a)==5*m and Q(85,100)<C<1,"support/gap coefficient")
    U,J,F0=primal(m,a,L)
    tlo,thi=Q(42),Q(43); rootX=2*10**9
    need(uexp(tlo)<rootX**2<lexp(thi),"log X")
    d=C*thi/(2*rootX); lam=5*d
    need(lam<1 and lexp(Q(22))*d>2*PU and d<PL/2,"zero error and support")
    ylower=Q(rootX**2)*(1-4*d)
    nodes=a+[Q(0)]; full=nodes[:0:-1]+nodes
    A0=sum(map(abs,full))/m
    Wmax=max(map(abs,full))
    slopes=[0]+[m*(b-a) for a,b in pairs(full)]+[0]
    var1=sum(abs(b-a) for a,b in pairs(slopes))
    var0=sum(abs(b-a) for a,b in pairs(full))
    g0=var1/(4*PL**2)
    g1=(5*var1+2*var0)/(2*PL)
    wing=list(map(pos,nodes[m:]))
    H=wing[0]+sum(pos(b-a) for a,b in pairs(wing))
    Aprime=4*(1+lam/tlo)/(1-lam/2)
    Bprime=Aprime/(1-lam)
    D=F0-A0*(lam/2)**2/(1-(lam/2)**2)-Bprime*J
    Kzeros=2*g0+d*(Q(3,10)*g1+(3+Q(15,100)*22)*2*(10*PU*A0+g1))
    Kpow=(Wmax*(thi+6*d)**2/(1-2*d)*(1+5*C*thi/(2*(1-3*d)))
          /(2*loglo(2)*rootX))
    need(ylower>rootX**2/2 and ylower>rootX**2/4,"support lower bound")
    Ktriv=d*A0/(Q(rootX,2)*(ylower**2-1))
    K=Kzeros+2*Aprime*H+Kpow+Ktriv
    loss=C*C*thi**2/(4*rootX)
    need(C*tlo*loglo(2)/2 > uexp(Q(5,2)),"log gain")
    margin=Q(5,2)*U - loss*D - K
    print('U <=',up(U),'J <=',up(J),'F0 =',up(F0))
    print('Kzeros <=',up(Kzeros),'wing error <=',up(2*Aprime*H),
          'Kpowers <=',up(Kpow),'Ktriv <=',up(Ktriv))
    print('D >=',up(D-Q(1,10**15)),'K <=',up(K),'cD-U >=',up(C*D-U-Q(1,10**15)),
          'margin >=',up(margin-Q(1,10**15)))
    need(D>0 and C*D>=U and margin>Wmax*thi/rootX,"strict all-real ray failed")
    print('PASS strict all-real ray [4*10^18, infinity)')

def small(C):
    primes=[j for j in range(2,1450) if all(j%k for k in range(2,isqrt(j)+1))]
    K=0
    for p,q in pairs(primes):
        x=max(4,p)
        if x>1423:break
        need(q-x<C*sqrtlo(x)*loglo(x,140),"finite elementary gap")
        K+=1
    need(any(q>1423 for q in primes),"last prime verified")
    # The Buethe bridge: x>=1423, y=x+2 sqrt(x) is within source domain
    # for x<=4*10^18.  sqrt(y)<sqrt(x)+1, so theta(y)-theta(x)>0.1 sqrt(x)-1.95.
    need(Q(1,10)*sqrtlo(1423)>Q(195,100) and C*loglo(16)>2,"Buethe margin")
    need(4*10**18+4*10**9<=10**19,"Buethe domain")
    print('PASS',K,'elementary gap intervals; strict Buethe bridge numeric conditions')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('path',type=Path)
    p.add_argument('C',type=Q)
    p.add_argument('--fft',type=int,default=2**19)
    args=p.parse_args()
    explicit(*read(args.path),args.C,args.fft)
    small(args.C)
