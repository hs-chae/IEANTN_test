"""Exact rational enclosures and analytic-envelope checker; Python 3.10 stdlib only.

The mathematical consumers and proof of the monotonicity reductions are in
PNT.md, Weighted.md, Intervals.md, and Ramanujan.md. No floating-point
number affects any assertion or sign. Printing a floor is only for reporting.
"""
from fractions import Fraction as F
from math import factorial, comb
import json
import os
from pathlib import Path

SCALE=2**256

class I:
    def __init__(self,l,h=None):
        l=F(l)
        h=l if h is None else F(h)
        assert l<=h
        self.l=F((l*SCALE).__floor__(),SCALE)
        self.h=F((h*SCALE).__ceil__(),SCALE)
    def __add__(self,r):
        r=cast(r)
        return I(self.l+r.l,self.h+r.h)
    __radd__=__add__
    def __neg__(self): return I(-self.h,-self.l)
    def __sub__(self,r): return self+-cast(r)
    def __rsub__(self,r): return cast(r)+-self
    def __mul__(self,r):
        r=cast(r)
        a=[u*v for u in (self.l,self.h) for v in (r.l,r.h)]
        return I(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,r):
        r=cast(r)
        assert r.l*r.h>0, 'zero in denominator'
        return self*I(1/r.h,1/r.l)
    def __rtruediv__(self,r):return cast(r)/self
    def __pow__(self,n):
        if n<0: return (1/self)**(-n)
        if n==0: return I(1)
        if n%2: return self*(self**(n-1))
        u=self**(n//2)
        return u*u
    def lt(self,r): return self.h<cast(r).l
    def gt(self,r): return self.l>cast(r).h
    def floor_scaled(self,d): return (self.l*d).__floor__()
    def decimal_lower_floor(self,n=6): return F(self.floor_scaled(10**n),10**n)

def cast(r): return r if isinstance(r,I) else I(r)

def exp_pt(t,N=58):
    if t<0: return 1/exp_pt(-t,N)
    k=0
    while t>1:
        t/=2
        k+=1
    q=I(t)
    term=s=I(1)
    for j in range(1,N+1):
        term=term*q/j
        s+=term
    r=(term*q/(N+1))/(1-F(1,N+2))
    v=I(s.l,(s+r).h)
    for _ in range(k): v=v*v
    return v

def exp(t):
    t=cast(t)
    return I(exp_pt(t.l).l,exp_pt(t.h).h)

def log_unit(x,N=58):
    assert 1<=x<=2
    u=(I(x)-1)/(I(x)+1)
    u2=u*u
    un=u
    v=I(0)
    for k in range(N):
        v+=un/(2*k+1)
        un*=u2
    rem=un/((2*N+1)*(1-u2))
    return I((2*v).l,(2*(v+rem)).h)

LOG2=log_unit(F(2))

def log_pt(x):
    assert x>0
    if x<1: return -log_pt(1/x)
    b=x.numerator.bit_length()-x.denominator.bit_length()
    b-=x < 2**b
    return b*LOG2 + log_unit(x/2**b)

def log(x):
    x=cast(x)
    return I(log_pt(x.l).l,log_pt(x.h).h)

def atan_inverse(q,n=45):
    x=F(1,q)
    s=sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
    t=s+(-1)**n*x**(2*n+1)/(2*n+1)
    return I(min(s,t),max(s,t))

PI=16*atan_inverse(5)-4*atan_inverse(239)
HN=1024
HG=sum(F(1,k) for k in range(1,HN+1))-log(HN)
GAMMA=I((HG-F(1,2*HN)).l,(HG-F(1,2*(HN+1))).h)

def ei(x,n=150):
    """Positive-real Ei series; n+2>x ensures a geometric tail bound."""
    x=cast(x)
    assert x.gt(0) and x.lt(n+2)
    term=I(1)
    s=GAMMA+log(x)
    for k in range(1,n+1):
        term=term*x/k
        s+=term/k
    tail=(term*x/(n+1)/(n+1))/(1-x/(n+2))
    return I(s.l,(s+tail).h)

def moments(x):
    return x/(2*PI)*(log(x/(2*PI))-1)+F(7,8)

def numeric_checks():
    """Small auditable guard inequalities for the paper derivations."""
    c=log(2*PI)
    assert PI.gt('3.14159') and PI.lt('3.14160')
    assert GAMMA.gt('.577') and (2+GAMMA-log(4*PI)).lt('.047')
    assert LOG2.gt('.69') and LOG2.lt('.70')
    assert c.gt('1.8') and c.lt('1.9')
    assert ((2-c)/LOG2-ei(LOG2)).gt(-1)
    assert ((2-c)/LOG2+c/8-ei(LOG2)).lt(1)
    assert (exp(LOG2/2)/LOG2**2).lt(3)
    assert (exp(LOG2/2)/LOG2**3).lt('4.4')
    assert (exp(4)/8**3).lt('4.4')
    M=moments(12)
    assert M.gt(0) and (M+F('.28')*log(12)).lt(1)
    assert (F('.56')*(log(12)+1)/12+M/6-log(6/PI)**2/(2*PI)).lt('.130')
    assert (F('.56')*log(10**7)/10**7).lt('.000001')
    assert (F('.75')*log(35)-LOG2-F('1.5')).gt('.473')
    assert (log(F(35,2))**2/35).lt('.235')
    assert (log(35)/35).lt('.102')
    assert (log(F(35,2))-F('.5')-F('.28')*PI).gt(0)
    assert (F('1.5')-GAMMA).lt('.923')
    assert (((F('1.5')-GAMMA)**2)/2+F(5,8)-PI**2/24).lt('.64')
    assert (F(35,2)**2*exp(F(-35,4))/(8*PI)).lt('.01')
    assert (1+F('.00000075')+3*exp(F(-35,6))).lt('1.01')
    assert (1+F('.00000075')+3*exp(-2)).lt('1.407')
    assert (4*PI*exp(F('17.5'))/35).gt(10**7)
    assert (35*exp(F('-17.5'))/(2*PI)).lt('.00000015')
    assert (35**3*exp(F('-17.5'))/(2*PI)).lt('.00018')
    assert (I(12)**2*exp(-6)/(8*PI)).lt('.015')
    assert (I(8)**2*exp(-4)/(8*PI)).lt('.05')
    assert (I('1.045')+F('5.25')*exp(-4)).lt('1.142')
    assert (F('.21625')*log(4)*24/(24+log(4))-F('.047')*(1*3+F(4,24))-F('1.045')*24*exp(-12)).gt('.13')
    assert (F('.047')+F('.094')/35+F('4.5')*35*exp(F('-17.5'))).lt('.05')
    assert (F('1.045')+F('5.25')*exp(F(-35,6))).lt('1.061')
    assert (F('.955')-F('1.045')*exp(F('-17.5'))).gt('.954')
    assert (I('2.09')+F('7.875')*exp(-4)+F('.047')*(3+F(4,24))+exp(-12)/(2*(exp(48)-1))).lt('2.39')
    assert (I('1.142')+F('.047')*(1+F(3,24)+F(4,24**2))+F('2.945')*exp(-12)).lt('1.20')
    d0=I(12)-log(24)-F(1,4)
    assert (d0/24).gt('.35')
    assert (log(2*PI*F('.35'))-F(1,4)-1+GAMMA).gt('.113')
    dmax=48*exp(-12)
    assert dmax.lt('.000295')
    assert (2*dmax*(1+F(7,3)*(1+F('.28')*log(1/dmax))+F('.896'))).lt('.0065')
    assert (F('1.0002')*F('1.001')*24*exp(-12)*(F('96.0192')+log(48))).lt('.0155')
    assert (2*(I(75)/2-log(75)-F(1,4))/75).lt('.8784')

def small_theta_and_weighted():
    C=F('1.00000075')
    t=I(0)
    prime=[]
    for m in range(2,1424):
        if all(m%p for p in prime if p*p<=m):
            t+=log(m)
            prime.append(m)
        if m>=6: assert t.gt(F('.48')*(m+1))
        if m>=17: assert t.gt(F('.60')*(m+1))
    L=F('5.7')
    y=exp(L/3)
    assert y.gt(6) and exp(L/2).gt(17)
    A=2*C-F('.60') + (F('1.5')*C+y/(y-1)*(F('1.5')*C-F('.48')))*exp(-L/6) + LOG2*exp(-L/2)/2
    wu=F('.94')+A+F('.047')*(1+3/L+4/L**2)+(log(2*PI)+2*C-F('.60'))*exp(-L/2)
    v=wu*exp(-L/2)/L
    assert (wu/(1-v)).lt(3*L**2/(8*PI))


def P(u,N=16):
    return sum(F(factorial(k),1)/u**k for k in range(N))

N=16
Plo=[F(factorial(k)) for k in range(N+1)]
Phi=Plo[:N]+[4*Plo[N]]
# Positive series for L/(L-1)*Plo(L-1), followed by upper square.
cs=[sum(Plo[k]*comb(m,k) for k in range(min(m,N)+1)) for m in range(2*N+1)]
hs=[cs[m]-sum(Phi[k]*Phi[m-k] for k in range(N+1) if 0<=m-k<=N) for m in range(2*N+1)]
assert hs[:6]==[0,0,0,0,1,14]
h=hs[4:]

def baseline(a,b):
    """Polynomial lower bound uniformly L>=a, and L<=b if b not None."""
    lo=F(0) if b is None else 1/b
    hi=1/a
    return sum(c*(lo if c>=0 else hi)**j for j,c in enumerate(h))

C0=F('1.00000075')
Ceps=F('0.0000000000124')

def anchors():
    E=exp(24)
    mid=ei(24)
    assert (E*P(F(24),N+1)/24).lt(mid)
    assert mid.lt(E*(P(F(24),N)+4*F(factorial(N),24**N))/24)
    assert ei(12).lt(F('1.113')*exp(12)/12)
    assert ei(F(35,2)).lt(F('1.067')*exp(F(35,2))/F(35,2))
    def app(u): return exp(-u/2)*(u**2/(8*PI)+F('.094')/u)+5*u*exp(-u)
    assert (F('1.113')+app(F(12))).lt('1.13')
    assert (F('1.067')+app(F(35,2))).lt('1.07')
    assert (4*LOG2+2*exp(-1)).lt(4)
    def q3(u): return 4*(exp(-u/6)+exp(-u/4)+exp(-3*u/10)+u/LOG2*exp(-u/3))
    assert (F('1.13')+q3(F(24))).lt('1.3')
    assert (F('1.07')+q3(F(35))).lt('1.1')
    assert (log(24)/(8*PI)).gt(F('1.3')/24+F('.094')/24**2+5*exp(-12))
    H=F(3*10**12)
    k=36
    eta=k/H
    Z=(log(H/(2*PI))**2/(2*PI)+F('.131'))*exp(eta)
    assert (I('.000022')**2).gt(eta*eta+k*eta)
    sh=(exp(k)-exp(-k))/2
    R=exp(eta+F('.000022'))*(k/sh)*(2*log(2*H)/PI+log(2*H)/(PI*k))
    assert Z.lt(116)
    assert (R+eta*exp(2*eta)).lt(Ceps)
    # Centered Logan window: exact half-first moment from the I_1 series.
    term=I(k)/2
    bessel=term
    for j in range(1,101):
        term*=F(k*k,4*j*(j+1))
        bessel+=term
    tail=term*F(k*k,4*101*102)/(1-F(k*k,4*101*102))
    assert ((bessel+tail)/(2*sh)).lt('.066')
    H1=F('1.05')*H
    assert (1-(H/H1)**2-(1/H1)**2)>F('.3')**2
    near=F('.05')*log(H1/(2*PI))/PI+F('.56')*(log(H)+log(H1))/H
    distant=log(H1)/(F('.3')*eta*PI*H1)
    assert (near+distant).lt('1.25')
    assert (F('1.25')*exp(F('.000022'))*k/sh+eta**2*exp(eta)/2).lt('2.2e-14')
    assert (2*exp(eta)*(F('.066')*eta+F('5e-16'))*(1+eta/100)).lt('1.59e-12')
    assert (F(15)*log(10)+eta).lt(35)
    assert (I('117.407')+F('1.9')*exp(-6)).lt(118)
    assert (exp(6)/12*(F('1.95')+F('3.9')/12+F('19.5')/144)).lt(82)
    assert (19*log(10)).gt(F('43.7'))

def error(a,b,model,neg):
    """Upper bound for u^4 epsilon(u) on u in [a,b]."""
    if model=='rh':
        s=a/2-log(a)
        psi=(s*s+F('1.662')*s+F('1.148')+a)/(2*PI)+F('.14')
        q=F('1.1') if neg else F('-.99')
        return a**4*( exp(-a/2)*(psi+F('.094')/a+q)+5*a*exp(-a) )
    if model=='buthe':
        return a**4*exp(-a/2)*(F('1.95')+F('3.9')/a+F('19.5')/a**2) if neg else I(0)
    if model=='height':
        assert b is not None
        return a**4*(118*(1+3/a)*exp(-a/2)+82*a*exp(-a)) + Ceps*(b**4+F('1.2')*b**3)
    if model=='center':
        assert b is not None and a>=100
        eta=F('1.59e-12')*b/(b-35)+F('2.2e-14')
        return a**4*(118*(1+3/a)*exp(-a/2)+82*a*exp(-a)) + eta*b**4 + F('1.2')*Ceps*b**3
    raise ValueError(model)

def prove_cell(a,b,model):
    a=F(a)
    b=None if b is None else F(b)
    vb=None if b is None else b-1
    rl=error(a-1,vb,model,True)
    rr=error(a,b,model,False)
    # This is an upper bound on the scaled penalty on the whole cell.
    pen=(a/(a-1))**5*rl+2*(P(a,N)+4*F(factorial(N),1)/a**N)*rr+rr*rr/a**4
    lb=I(baseline(a,b))-pen
    m=lb.floor_scaled(10**6)
    assert m>0, (model,a,b,m)
    return dict(a=str(a), b=str(b) if b is not None else None, marginMillionths=m,
                rl_bound=str(F((rl.h*10**12).__ceil__(),10**12)),
                rr_bound=str(F((rr.h*10**12).__ceil__(),10**12)))

PLANS={
    'rh':['38.95','39.06','39.25',40,42,45,50,60,None],
    'buthe':['28.12','28.2',29,31,36,'43.7'],
    'height':[42,44,50,80,160,300,380,400,407],
    'center':[101,160,280,420,560,620,650,665],
}

def run():
    numeric_checks()
    anchors()
    small_theta_and_weighted()
    # Verify the stronger asymptotic lower envelope.
    a=F(60)
    base2=h[2]+sum(min(F(0),c)/a**(j-2) for j,c in enumerate(h) if j>=3)
    rl=error(a-1,None,'rh',True)
    rr=error(a,None,'rh',False)
    pen=a**2*((a/(a-1))**5*rl+2*(P(a,N)+4*F(factorial(N),1)/a**N)*rr+rr*rr/a**4)
    assert (I(base2)-pen).gt(142)
    assert exp('28.12').lt(1630650286564)
    records={}
    for model, knots in PLANS.items():
        out=[]
        for a,b in zip(knots,knots[1:]):
            cell=prove_cell(a,b,model)
            print(model,cell)
            out.append(cell)
        records[model]=out
    Path(os.environ.get('ENVELOPE_OUT', Path(__file__).with_name('ramanujan_cells.json'))).write_text(json.dumps(records,indent=2)+chr(10))

if __name__=='__main__': run()
