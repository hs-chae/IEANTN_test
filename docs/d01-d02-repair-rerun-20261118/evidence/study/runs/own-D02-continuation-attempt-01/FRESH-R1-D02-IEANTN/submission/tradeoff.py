"""Alternative use of D01 with no QRH premise, not a matched improvement."""
from verify import I,D,c,pi,fac,C,factpoly,connection
L0=I(200)
ep=3*(12-L0).exp()+(I('1.2')*c+351*(-L0/2).exp())/L0**2
assert ep.b<D('4e-17')
def error(L):
    return (I('4e-17')*L*(200-L).exp()+
      L**2/64*(-L/8).exp()*(1+1/(I('.855')*L))+
      3*(-L/2).exp()*(1+1/(I('.48')*L))+
      13*L*(-L).exp()+3*fac(19)/L**19)
for n in [4,5,6,8,12,17]:
    for a in range(max(201,8*(n+3)+2),1000):
        L=I(a); z=L-1
        em=error(z)
        if (I('3.1')*L**(n+1)*em).b<C[n+1]:
            assert (L/z+2*factpoly(L)+em).b<D('3.1')
            print('D01 (without QRH) Ramanujan tail:',n,a)
            if n==4:connection(60,a,'1',False,None,10)
            break
    else:raise ValueError(n)
# Mertens, scaled relative to L or L^2 as applicable, with V<=4e^-L/2+10e^-2L/3.
V=(4*(-3*L0/8).exp()+10*(-I(2)*L0/3+L0/8).exp())/L0**2
l=(9+72/L0)/64+V
w=(9+128/L0+1024/L0**2)/64+V
assert (l*(l*L0*(-L0/8).exp()).exp()).b<D('.147')
assert w.b<D('.152')
print('D01 (without QRH) Mertens: .147 L and .152 L^2 exponents, L>=200')
