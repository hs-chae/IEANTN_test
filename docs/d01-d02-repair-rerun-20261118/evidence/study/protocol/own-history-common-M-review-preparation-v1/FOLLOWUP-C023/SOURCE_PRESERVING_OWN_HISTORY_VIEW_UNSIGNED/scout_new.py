"""Proposal generation only: no mathematical conclusion from this floating-point routine."""
import d02_ram_new as R
import d02_density_new as Z
import math
from functools import lru_cache
from math import exp,factorial as fac
def generate():
 for D in [Z.D,Z.D0]:
    d=float(D); q=float(Z.q); s=29.9
    @lru_cache(None)
    def f(L,m):
        u=Z.mass(D,m)
        return float(u[-1][1])+sum(float(w-z)*exp(float(p-1+D)*L)
                                    for (_,w),(p,z) in zip(u,u[1:]))
    @lru_cache(None)
    def b(L):
        return (((L/3+1)**2/6+2)*exp(-(.3-d)*L)+2.091*L*exp(-(1/3-d)*L)+f(L,1))
    @lru_cache(None)
    def j(L):return (13*exp(-(.3-d)*L)+f(L,2))/Z.H
    def p(L):return b(L)*exp(-d*L)
    def re(L,sign):
        z=exp(-L/2)
        a=min(q+113.67*z,p(L))
        v=a+(1.000000147*z+1.78*exp(-2*L/3) if sign==1 else -.9999*z)
        if L<=58:v=min(v,.0397888*L*L*z)
        return (v+(.155*z+2.6*j(L)*exp(-d*L))/L+.074*L*exp(s/2-L)
                  +(2.36*z/L if sign==1 else -1.9998*z/L*(1-exp((s-L)/2))))
    def H(n,L):return sum(fac(i)/L**i for i in range(n+1))
    def V(n,L):
        B,A=R.ANC[n]
        return A*L*exp(-L)+(B/(B-n-2))*fac(n+1)/L**(n+1)
    def bound(L,jj=6,n=20):
        C,S=R.polys(n)
        e=V(n,L)+re(L,-1)
        a=re(L-1,1)
        return (sum(C[k]/L**(k-jj) for k in range(jj,n+1))
               -sum(S[k]/L**(k-jj) for k in range(n+1,2*n+1))
               -L**jj*(L/(L-1)*a+e*(2*H(n,L)+e)))
    print('strip',d,flush=True)
    vals=[(bound(40+k/100),40+k/100) for k in range(700,16000)]
    for start in [47,47.64,47.647,47.68,47.75,47.8,47.97,48,48.1,48.3,48.5,49,50,52,55,60,150,160,165,170,175,180]:
        print('join',start,min((v,L) for v,L in vals if L>=start),flush=True)
    def end(L,jj,n,z):
        C,S=R.polys(n)
        P,W=b(L-1),j(L-1)
        def t(u):return ((P+2.6*W/u)*exp(-d*u)+(1.000000147+2.515/u)*exp(-u/2)
                        +1.78*exp(-2*u/3)+.074*u*exp(s/2-u))
        e=V(n,L)+t(L)
        return sum(C[k]*L**(jj-k) for k in range(jj,n+1))-z-sum(S[k]*L**(jj-k) for k in range(n+1,2*n+1))-L**jj*(L/(L-1)*t(L-1)+e*(2*H(n,L)+e))
    for n,js in [(20,range(6,21)),(40,range(21,41)),(80,range(41,81))]:
        onsets=[]
        for jj in js:
            a=max(math.floor(n/d)+1,R.ANC[n][0]+1)
            z=100 if jj==6 else 0
            h=5000
            assert end(h,jj,n,z)>0
            while a<h:
                m=(a+h)//2
                if end(m,jj,n,z)>0:h=m
                else:a=m+1
            onsets.append(a)
        print(n,onsets,flush=True)
    for n in (20,40,80):
        jj=n; z=R.polys(n)[0][jj]/2
        a=max(math.floor(n/d)+1,R.ANC[n][0]+1)
        while end(a,jj,n,z)<=0:a+=1
        print(n,'half',a,flush=True)
    yield D,p,b,j
if __name__=='__main__':
 for _ in generate():pass
