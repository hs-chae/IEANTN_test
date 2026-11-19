#!/usr/bin/python3.10
from cert import *
pi=I('3.14159265358979323846','3.14159265358979323847')
e=I(1).exp()
def coeff(v):
    v=I(v)
    return ((v-2*(v/(pi*e)).log())**2-4)/(8*pi)
@lru_cache(None)
def bound(l,u): # combined normalized v^4 error on [l,u] within [34,58]
    assert l>=34 and u<=58
    v=I(l)
    c=coeff(u)+I('1.000000147')+I('1.78')*(-v/6).exp()
    return mini(psierr(l,0), c*(v**4+v**3/(Q(1,2)-Q(2,34)))*(-v/2).exp() +
                 2*v**5*(-v+17).exp()/25)
def los(l,u,signed):
    d=bound(l,u)
    m=bound(l-1,u-1)*(I(l)/(l-1))**5
    return m if signed else m+2*Alim(l)*d+d*d/I(l)**4
def chk(l,u,t,sign):
    l,u=Q(l),Q(u)
    f=[g(j+4)-(t[j] if j<len(t) else 0) for j in range(24)]
    a=D('Infinity')
    while l<u:
        r=min(u,l+Q(1,256))
        b=sum(I(f[j])/I(r if f[j]>=0 else l)**j for j in range(len(f)))
        a=min(a,(b-los(l,r,sign)).a)
        l=r
    print('early',t,u,'signed' if sign else 'absolute',f'{a:.9E}')
    assert a>0
def main():
    assert (2*pi*pi*(I(17).exp())/34).a>D('10000000')
    assert (2*pi*pi*(I(29).exp())/58).b<D('3000000000000')
    assert I('36.9').exp().b<D('11500000000000000')
    chk('36.9','39.47',[0],True)
    chk('39.47','39.7',[0],False)
    chk('40.5','40.9',[Q('0.5')],False)
    chk('42.3','42.6',[Q('0.9')],False)
    chk('42.9','43.2',[1],False)
    chk('47.4','47.7',[1,14],False)
    chk('49.1','49.4',[1,14,78],False)
if __name__=='__main__':main()
