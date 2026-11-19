"""Rigorous polynomial Ramanujan rungs through degree 36 (see ram_high.md)."""
from ram_repair import Q, expb, eL, logb, series, theta_new
from math import factorial as fac, comb
from functools import lru_cache
N=40
B=64
Anchor=10**5
@lru_cache(None)
def eh(t):
    d=10**150
    if t<=-350:
        assert eL**350>d
        return Q(1,d)
    return Q((d*expb(t)[1]).__ceil__(),d)
def hi(t,p):
    return (p+Q('8e-12')/t)*eh(-t/8)+7*eh(-t/2)/t+Q('3.21')*t*eh(20-t)
def H(u):return sum(Q(fac(n))/u**n for n in range(N+1))
def V(u):return Anchor*u*eh(-u)+Q(32,11)*fac(41)/u**41
def anchor():
    u=Q(B); n=240
    E,F=series(Q(1),98)
    A,D=logb(u)
    T=sum(u**k/Q(k*fac(k)) for k in range(1,n+1))
    tail=u**(n+1)/(Q((n+1)*fac(n+1))*(1-u/(n+2)))
    l=T+A-F**B*H(u)/u
    r=T+tail+D+1-E**B*H(u)/u
    print('order-40 PV anchor computed residual enclosures',float(l),float(r),flush=True)
    assert 0<l<r<Anchor
S=[sum(fac(i)*fac(k-i) for i in range(max(0,k-N),min(k,N)+1)) for k in range(2*N+1)]
C=[sum(comb(k,i)*fac(i) for i in range(k+1))-S[k] for k in range(N+1)]
assert C[:7]==[0,0,0,0,1,14,145] and min(C[4:])>0
@lru_cache(None)
def cost(a, j):
    p=theta_new(a-1)
    e=V(a)+hi(a,p)
    return a**j*(a/(a-1)*hi(a-1,p)+e*(2*H(a)+e))
def surplus(a,j,z):
    return (sum(Q(C[k])*a**(j-k) for k in range(j,N+1))-z
             -sum(Q(S[k])*a**(j-k) for k in range(N+1,2*N+1))-cost(a,j))
# Strict lower profiles of every degree j-5, plus half the degree-36 term.
ONSETS=[720,757,793,830,866,903,939,976,1013,1049,
        1086,1122,1159,1196,1232,1269,1306,1342,1379,1419]
ROWS=[(j,a,0) for j,a in enumerate(ONSETS,21)] + [(40,1431,Q(C[40],2))]
if __name__=='__main__':
    anchor()
    assert hi(Q(719),theta_new(Q(719)))<1
    for j,a,z in ROWS:
        u=surplus(Q(a),j,z)
        print('high profile',j,a,z,'slack in C_j units',float(u/C[j]),flush=True)
        assert 0<=z<C[j] and a>8*N and u>0
