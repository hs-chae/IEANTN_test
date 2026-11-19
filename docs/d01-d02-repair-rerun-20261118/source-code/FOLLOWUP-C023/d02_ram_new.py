"""Exact whole-cell and single-endpoint-plus-monotonicity checks."""
from math import comb, factorial as fac
from functools import lru_cache
import ram_repair as old
from d02_density_new import Q,D,D0,q,CT,F,J,eu,el,ep
s=Q('29.9')
K=Q('2.6')
def pcap(a,d,panels):
    h=q+CT*eu(-a/2)
    if a>=40:
        b=Q((panels*a).__floor__(),panels)
        # Frozen coefficient but no freezing of the exponential.
        h=min(h,F(b,d)*eu(-d*a))
    return h
def reanchor(a,b,d,panels=16):
    c=Q('.0397888')
    pp=pcap(a,d,panels)
    thick=pp+Q('1.000000147')*eu(-a/2)+Q('1.78')*eu(-2*a/3)
    thin=pp-Q('.9999')*el(-b/2)
    if b<=58:
        sym=c*a*a*eu(-a/2)
        thick,thin=min(thick,sym),min(thin,sym)
    t=(Q('.155')*eu(-a/2)+K*J(a,d)*eu(-d*a))/a+Q('.074')*a*eu(s/2-a)
    return thick+t+Q('2.36')*eu(-a/2)/a,thin+t-Q('1.9998')*el(-b/2)/b*(1-eu((s-a)/2))
def cost(a,b,j,d,panels=16):
    u,v=a-1,b-1
    em=old.err(u,v)
    if u>=40: em=min(em,reanchor(u,v,d,panels)[0])
    # Main uses the upper delta. Calls here are all beyond the early signed branch.
    e=Q(0) if b<=old.A0 else old.err(a,b)
    if a>=40:e=min(e, old.reanchor_up(a,b),reanchor(a,b,d,panels)[1])
    e+=old.V(a)
    assert old.H(b)+e>0
    square=a**j*e*(2*old.H(b)+e) if e<0 else b**j*e*(2*old.H(a)+e)
    return b**j*a/(a-1)*em+square

def adapt(a,b,j,z,d=D,panels=16,depth=17):
    a,b,z=Q(a),Q(b),Q(z)
    P=sorted({a,b}|{Q(t) for t in ('40','41','43.7','44.7','58','59','185','186') if a<Q(t)<b})
    todo=list(reversed(list(zip(P,P[1:]))))
    best=Q(10**20);n=0
    while todo:
        f,g=todo.pop()
        slack=old.rem(f,g,j)-cost(f,g,j,d,panels)-z
        if slack>0:
            best=min(best,slack)
            n+=1
        elif g-f<=Q(1,2**depth):
            return False,n,slack,f,g
        else:
            h=(f+g)/2
            todo.extend([(h,g),(f,h)])
    return True,n,best,a,b

@lru_cache(None)
def H(n,u):return sum(Q(fac(i))/u**i for i in range(n+1))
# n : (anchor u, upper bound on unnormalized residual).
# n=20 used at u>=40 with its better anchor.
ANC={20:(40,170),40:(64,100),80:(128,11000)}
def anchor(n):
    B,A=ANC[n]
    T=Q(B)
    m=5*B
    part=sum(T**k/Q(k*fac(k)) for k in range(1,m+1))
    end=T**(m+1)/(Q((m+1)*fac(m+1))*(1-T/(m+2)))
    p,r=old.logb(T)
    l,u=ep(T)
    lower=part+p-u*H(n,T)/T
    upper=part+r+1+end-l*H(n,T)/T
    print('li anchor',n,B,float(lower),float(upper),flush=True)
    assert 0<lower<upper<A
def V(n,u):
    B,A=ANC[n]
    return A*u*eu(-u)+Q(B,B-n-2)*fac(n+1)/u**(n+1)
@lru_cache(None)
def polys(n):
    S=[sum(fac(i)*fac(k-i) for i in range(max(0,k-n),min(k,n)+1)) for k in range(2*n+1)]
    C=[sum(comb(k,i)*fac(i) for i in range(k+1))-S[k] for k in range(n+1)]
    assert C[:7]==[0,0,0,0,1,14,145] and min(C[4:])>0
    return C,S
@lru_cache(None)
def frozen(a,d):
    return F(a-1,d),J(a-1,d)
def de(t,P,W,d):
    # Discard the favorable prime-power sign in the analytic tail, for monotonicity.
    return ((P+K*W/t)*eu(-d*t)
            +(Q('1.000000147')+Q('2.515')/t)*eu(-t/2)
            +Q('1.78')*eu(-2*t/3)+Q('.074')*t*eu(s/2-t))
def end(a,j,z,n,d=D):
    a,z=Q(a),Q(z)
    assert a>n/d and a-1>=ANC[n][0] and a>=41
    C,S=polys(n)
    assert 0<=z<C[j]
    P,W=frozen(a,d)
    h1,h2=de(a-1,P,W,d),de(a,P,W,d)
    e=V(n,a)+h2
    loss=a**j*((a/(a-1))*h1+e*(2*H(n,a)+e))
    val=sum(Q(C[k])*a**(j-k) for k in range(j,n+1))-z
    tail=sum(Q(S[k])*a**(j-k) for k in range(n+1,2*n+1))
    assert h1<1
    return val-tail-loss

if __name__=='__main__':
    import sys
    if sys.argv[1:] == ['anchors']:
        for n in ANC:anchor(n)
