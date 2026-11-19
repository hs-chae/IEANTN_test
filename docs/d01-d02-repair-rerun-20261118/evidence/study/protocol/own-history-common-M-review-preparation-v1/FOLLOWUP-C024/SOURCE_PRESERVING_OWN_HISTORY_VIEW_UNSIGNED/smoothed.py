"""Average in log coordinate with an exact inverse-square zero mass."""
from spectral import *
from power import coeff as co_old
@lru_cache(None)
def squaremass(s):
    p=F(8,3)*(1-s); q=5-2*s; z=2-p
    def d(T,AT,u,v):
        a=I(1); S=a
        for i in range(1,5):
            a=a*(q-i+1)/(z*AT); S+=a
        # Includes conjugates and the factor 2 from differentiating T^-2.
        return 4*u*exp(q*log(AT)-z*AT)*S/z+2*v*(AT*AT+AT+I('.5'))/T**2
    u,v=next((u,v) for a,u,v in reversed(tab) if a<=s)
    return minI(d(Hf,Af,u,v),d(H,A,I('4.9')*exp(p*log(3)),I('51.5')))
@lru_cache(None)
def w2(b):
    g=mesh(b)
    ds=[]
    for s in g[:-1]:
        d=squaremass(s)
        ds.append(min(d.b,ds[-1] if ds else d.b))
    return [(g[-1],I(ds[-1],ds[-1]))]+[(g[i],I(ds[i-1]-ds[i],ds[i-1]-ds[i])) for i in range(1,len(ds))]
@lru_cache(None)
def kernel(a,z,b):
    t=I(a,z)
    return I('3.1e-12')*exp(-t/4)+exp(-(1-b)*t)*positive_sum(w2(b),t,b)
def sm(t,b,h):
    t,h=I(t),I(h)
    return exp(h)*(h/2+I('117.02')*exp(-t/2)+2*kernel(t.a,t.b,b)/h+I('1.84')*exp(-t))
def oldC(t,b):
    return positive_sum(co_old(b),I(t),b)+(I(t)**2/(9*I('6.28'))+I('1.8642'))*exp(-(b-s0)*I(t))+I('2.091')*I(t)*exp(-(b-F(2,3))*I(t))
def combined(t,b):
    t=I(t)
    return minI(C(t,b),oldC(t,b))*exp(-(1-b)*t)
def diagnostics():
    less(log(I(H)/(2*PI))**2/I('6.28')+I('1.8642'),117.02)
    from math import sqrt
    for b in [Q,J]:
        for z in ([174,176,178,179,180,181,182,185,190,200] if b==Q else [155,157,159,160,161,162,163,164,165,166,168,170,175,180,185,190,200]):
            t=I(z)
            K=approx(kernel(t.a,t.b,b))[1]
            h=f'{2*sqrt(K):.8e}'
            print(b,z,h,approx(sm(t,b,h))[1],approx(combined(t,b))[1],flush=True)
if __name__=='__main__': diagnostics()

