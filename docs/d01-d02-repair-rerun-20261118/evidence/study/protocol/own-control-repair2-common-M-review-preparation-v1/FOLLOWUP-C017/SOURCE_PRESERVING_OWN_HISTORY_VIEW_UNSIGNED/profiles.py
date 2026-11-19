from intervals import *
from functools import lru_cache
from math import factorial,comb
H=3*10**12
ell=I(H).ln()
s0=I(77)/100
s0i=616
basecap=700
newcap=675
CL=I(116)
CL2=I('.1')
c0=I('1.0001')
sourcefloor=PI/H

def ef(a,u): return (-a*I(u)).exp()
def X(u):return I(u).exp()
def powterm(u):
    return I('1.08')*ef(I('.5'),u)+u/3*ef(I(2)/3,u)+u*u/(4*LN2)*ef(I('.75'),u)
@lru_cache(None)
def dat(j):
    s=I(j)/800
    p=I(8)/3*(1-s); q=5-2*s
    d=1-p-q/ell; d2=1-2/ell
    g=I('9.8')*(p*I(3).ln()+q*ell.ln()+(p-1)*ell).exp()
    c=103*ell**2/H
    return (g/d+c/d2, g,c,d,d2)

def spec(u,cap,A,prim=False,damp=None):
    # Evaluation of an upper bound. Uses nonnegative collected coefficients.
    z=ef(I(1)/800,u)
    W=CL2 if prim else CL
    ds=[]
    for j in range(s0i,cap):
        B,g,c,d,d2=dat(j)
        if prim:
            B=2/H*(g/(1+d)+c/(1+d2))
        elif damp is not None:
            # Weighted density integral, also bounded by undamped B.
            a=damp
            if a.r<=1:
                B=mini(B,g*2*a/(1+d)+c*2*a/(1+d2))
            elif a.l>=1:
                def f(d):
                    power=a.power(-d)
                    return (1-power)/d+2*power/(1+d)
                B=mini(B,g*f(d)+c*f(d2))
        ds.append(mini(A,B))
    # Positive coefficients, including last entry, used for interval bounds.
    coeff=[A-ds[0]]+[ds[k-1]-ds[k] for k in range(1,len(ds))]+[ds[-1]]
    poly=I()
    for v in coeff: poly=poly*z+maxi(0,v)
    return W*ef(I('.5'),u)+A*ef(s0,u)+ef(1-I(cap)/800,u)*poly

def primitive(u,cap):
    return spec(u,cap,I(10)/H,prim=True)+2*ef(1,u)

def U(u):
    return ((u/4)**2/2+32*u/4+64)/6

def spectral(u,cap,h=None):
    if h is None:
        h=ef(I('.25'),u)
        A=U(u)
        s=spec(u,cap,A)
    else:
        h=I(h)
        a=2/(H*h)
        if a.r<=1:
            A=a*(ell+1)/3
        else:
            v=maxi(0,a.ln())
            A=(ell*v+v*v/2+2*(ell+v+1))/6
        s=spec(u,cap,A,damp=a)
    return (1+2*h)*(h/2+s)+2*ef(1,u)


def continuous_spectral(u,cap):
    """Closed majorant for continuous density integration; u>=140."""
    u=I(u)
    h=ef(I('.25'),u); A=U(u)
    a=1-I(cap)/800
    return (1+2*h)*(h/2+CL*ef(I('.5'),u)+A*(ef(s0,u)+ef(1-s0,u))
           +dat(cap)[0]*u/(u-97)*ef(a,u))+2*ef(1,u)

def source_bounds(u):
    from pathlib import Path
    import json
    if u.l < LN2.r: return []
    out=[I('9.22022')*u.power(I('1.5'))*ef(I('.8476836'),u.power(I('.5')))]
    for k,b in enumerate(('.77','.85','1.66','8.16','59.18')):
        out+=[I(b)/u**k]
    for t,b,*_ in SOURCE_DATA['steps']:
        if u.l>=t: out+=[I(b)]
    for t,A,B,C,RR,*_ in SOURCE_DATA['shapes']:
        if u.l>=t:
            v=u/I(RR)
            out+=[I(A)*v.power(I(B))*ef(I(C),v.power(I('.5')))]
    return out
from pathlib import Path
import json
SOURCE_DATA=json.loads(Path(__file__).with_name('source_tables.json').read_text())

def evalT(u,adaptive):
    T=I(H)
    if adaptive: T=maxi(I(10**7),mini(T,2*PI**2*X(u/2)/u))
    return T

def ch(u,with_weight=False,adaptive=False):
    T=evalT(u,adaptive)
    y=(T/(2*PI)).ln()
    c=y*y/(2*PI)-y/(6*PI)
    return PI/(T-1)+c*ef(I('.5'),u)+(0 if with_weight else PI**2/(3*T**2))

def err(u,cap,extra=False):
    u=I(u)
    B=[sourcefloor+I('113.67')*ef(I('.5'),u)]+source_bounds(u)
    if u.l>I(59).ln().r and u.r<=I('2.169e25').ln().l:
        B+=[u*u/(8*PI)*ef(I('.5'),u)]
    if u.l>=10 and u.r<=(I(10**13).ln()).l:
        B+=[I('.791')*ef(I('.5'),u)]
    if u.l>I(10**9).ln().r:
        if u.l>evalT(u,True).ln().r: B+=[ch(u,adaptive=True)]
        if u.l>ell.r: B+=[ch(u)]
    if u.l>=100:
        B+=[spectral(u,cap)]
        if u.l>=140: B+=[continuous_spectral(u,cap)]
        if extra:
            for h in ('1e-11','5e-12','2e-12','1e-12','5e-13','2e-13','1e-13','5e-14','1e-14','1e-15','1e-16'):
                B+=[spectral(u,cap,h)]
    if cap==newcap and u.l>=200:
        B+=[u*u/64*ef(I(5)/32,u)]
    return mini(*B)

def werr(u,cap):
    B=[sourcefloor+I('113.67')*ef(I('.5'),u),err(u,cap,True)+primitive(u,cap)]
    if u.l>I(10**9).ln().r:
        if u.l>evalT(u,True).ln().r: B+=[ch(u,True,True)]
        if u.l>ell.r: B+=[ch(u,True)]
    return mini(*B)

def p_err(u,cap,fast=False):
    u=I(u)
    up=I('1e6');dn=up
    if u.l>=37:
        if fast:
            B=minimal_e(u,cap)+6*spec_simple_prim(u,cap)/u+17000*u*ef(1,u)
        else:
            B=err(u,cap,True)+6*primitive(u,cap)/u+17000*u*ef(1,u)
        up=B-I('.988')*ef(I('.5'),u)
        dn=B+powterm(u)
    if u.r<=I(10**19).ln().l:
        alt=(I('1.95')+I('3.9')/u+I('19.5')/u**2)*ef(I('.5'),u)+2*u*ef(1,u)
        up=mini(up,alt);dn=mini(dn,alt)
    if u.r<=58:
        # theta Lemma 6; correction from below x=600
        alt=(u*u+2*u)/(8*PI)*ef(I('.5'),u)+1255*u*ef(1,u)
        up=mini(alt,up);dn=mini(alt,dn)
    if u.r<=(I('1.2e17').ln()).l:
        up=mini(up,2*u*ef(1,u))
    if u.l>=2000:
        pt=235*u.power(I('1.52'))*ef(I('.8'),u.power(I('.5')))
        up=mini(up,pt);dn=mini(dn,pt)
    return up,dn

def spec_simple_prim(u,cap):
    return I('.1')*ef(I('.5'),u)+20*ef(1-I(cap)/800,u)/H+2*ef(1,u)

def minimal_e(u,cap):
    # Cheap upper bounds used for tables; spectral coefficients certified below.
    c=[I('1.048e-12')+114*ef(I('.5'),u),ch(u,adaptive=True)]
    if u.l>=190:
        c+=[I('.014')*ef(I('.125'),u)]
    if cap==newcap and u.l>=170:
        c+=[I('.276')*ef(I(5)/32,u)]
    if cap==newcap and u.l>=200:
        c+=[I('.234')*ef(I(5)/32,u)]
    return mini(*c)

fact=[factorial(n) for n in range(42)]
d=[sum(fact[k]*comb(n,k) for k in range(min(n,20)+1))
   -sum(fact[k]*fact[n-k] for k in range(max(0,n-20),min(n,20)+1))
   for n in range(41)]
def horner(c,z):
    v=I()
    for b in reversed(c): v=z*v+b
    return v
def pol(u,n=0):
    return horner(fact[n:21],1/u)
def rem(u):
    if u.l<32:
        return u*ef(1,u)/2+12*fact[21]/u**21
    return 11*u*ef(1,u)+I(16)/5*fact[21]/u**21
def penalty(u,cap,fast=False):
    Ux,_=p_err(u,cap,fast)
    _,Dx=p_err(u-1,cap,fast)
    eps=Ux+rem(u)
    return u/(u-1)*Dx+(2*pol(u)+eps)*eps
def margin(u,cap,k=4,fast=False):
    # Coefficient after keeping terms d[4],...,d[k-1], in units x^2/(log x)^(k+2).
    return horner(d[k:],1/u)-u**k*penalty(u,cap,fast)

def vintegral(u):
    """V(e^u), using positive expansion and certified geometric tail."""
    u=I(u)
    assert u.l>LN2.r
    n=int(u.r)*4+160
    A,B=I(1),I(1)
    out=(u/LN2).ln()
    for j in range(1,n+1):
        A*=u/j; B*=LN2/j
        out+=(A-B)/j
    tail=(A*u/(n+1)**2)/(1-u/(n+2))
    return out+I(0,tail.r)

N=30
mfs=[factorial(k) for k in range(2*N+2)]
dN=[sum(mfs[k]*comb(n,k) for k in range(min(n,N)+1))
   -sum(mfs[k]*mfs[n-k] for k in range(max(0,n-N),min(n,N)+1))
   for n in range(2*N+1)]
dNplus=[max(0,x) for x in dN]
dNminus=[max(0,-x) for x in dN]
def remN(u):
    return 59*u*ef(1,u)+I(50)/18*mfs[N+1]/u**(N+1)

def penalty_tail(u,cap):
    # This function uses only positive factors and the unoptimized smoothing
    # branch, so its scaled monotonicity can be proved term by term.
    def jac(v):
        return mini(spectral(v,cap),continuous_spectral(v,cap))+6*spec_simple_prim(v,cap)/v+17000*v*ef(1,v)
    e=jac(u)+remN(u)
    return u/(u-1)*(jac(u-1)+powterm(u-1))+(2*horner(mfs[:N+1],1/u)+e)*e+horner(dNminus,1/u)

def mtail(u,cap,k):
    return horner(dNplus[k:],1/u)-u**k*penalty_tail(u,cap)
