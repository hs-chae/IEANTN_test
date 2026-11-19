"""FKS Table 8 (a1=.77) plus Dusart 2.3, with exact outward arithmetic."""
from functools import lru_cache
from D01_check import I,F,exp,log,less,approx,rng,PI
from power import Q,J,H,A,mass,low_part
Hf=3*10**12
Af=log(Hf)
tab=[('0.75','7.7980','4.1007'),('0.80','8.1611','3.6927'),
     ('0.81','8.5374','3.6127'),('0.82','8.9270','3.5327'),
     ('0.83','9.3299','3.4527'),('0.84','9.7462','3.3726'),
     ('0.85','10.1760','3.2925'),('0.86','10.6192','3.2124'),
     ('0.87','11.0756','3.1322')]
tab=[(F(s),I(u),I(v)) for s,u,v in tab]
s0=F(3,4)
def fks(s):
    u,v=next((u,v) for a,u,v in reversed(tab) if a<=s)
    p=F(8,3)*(1-s); q=5-2*s; z=1-p
    a=I(1); S=a
    for i in range(1,5):
        a=a*(q-i+1)/(z*Af); S+=a
    return 2*u*exp(q*log(Af)-z*Af)*S/z+2*v*(Af*Af+2*Af+2)/Hf

def minI(x,y): return I(min(x.a,y.a),min(x.b,y.b))
@lru_cache(None)
def mesh(b):
    # Exact nested partition with all Table 8 breakpoints.
    return sorted({s0+F(i,4096) for i in range(int((b-s0)*4096))} |
                  {s for s,_,_ in tab if s<b}|{b})
@lru_cache(None)
def coeff(b):
    g=mesh(b)
    ds=[]
    for s in g[:-1]:
        d=minI(fks(s),mass(s))
        # Monotonicize by taking the previous valid upper bound if better.
        # Collapse to exact upward-rounded rationals, so weights are nonnegative.
        ds.append(min(d.b,ds[-1] if ds else d.b))
    return [(g[-1],I(ds[-1],ds[-1]))]+[(g[i],I(ds[i-1]-ds[i],ds[i-1]-ds[i])) for i in range(1,len(ds))]

def positive_sum(co,t,edge):
    # Top exponent, then the remaining mesh points in descending order.
    z=I(1)
    prev=co[0][0]
    assert prev==edge
    v=co[0][1]
    for s,w in reversed(co[1:]):
        z*=exp(-(prev-s)*t)
        v+=w*z
        prev=s
    return v

@lru_cache(None)
def _C(a,z,b):
    t=I(a,z)
    v=positive_sum(coeff(b),t,b)
    return v+(t*t/(9*I('6.28'))+I('1.8642'))*exp(-(b-s0)*t)+I('2.091')*t*exp(-(b-F(2,3))*t)
def C(t,b):
    t=I(t); return _C(t.a,t.b,b)
def psi(t,b):
    return C(t,b)*exp(-(1-b)*I(t))
def D0(t,b):
    # Point cap CH2, original shape; intersects the new spectral bound.
    t=I(t); return minI(psi(t,b),I('1.048e-12')+I('113.67')*exp(-t/2))
def tailhigh(t,b):
    # psi explicit formula after one integration, |rho|*|1+a-rho| >= H |gamma|.
    t=I(t)
    return I('3.1e-12')*exp(-t/4)+exp(-(1-b)*t)*positive_sum(coeff(b),t,b)/H
def tail(t,b):
    t=I(t)
    return I('.0462')*exp(-t/2)+tailhigh(t,b)+I('1.84')*exp(-t)
def scaled(t,b):
    t=I(t)
    v=I('1.092')*exp(-(b-F(1,2))*t)
    j=I('.0462')*exp(-(b-F(1,2))*t)+I('3.1e-12')*exp(-(b-s0)*t)+positive_sum(coeff(b),t,b)/H+I('1.84')*exp(-b*t)
    return C(t,b)+(1+1/t)*j+v
def rel(c,t,b):
    t=I(t);return c/(1-c*exp(-(1-b)*t)/t)
if __name__=='__main__':
    for b in [Q,J]:
        print('exponent',b,'limit',approx(coeff(b)[0][1])[1],flush=True)
        for t in [155,158,160,162,163,164,165,166,167,168,175,180,185,186,200,220,250,300,500,1000,2300,10000,50000]:
            print(t,approx(psi(t,b))[1],approx(rel(scaled(t,b),t,b))[1],flush=True)

