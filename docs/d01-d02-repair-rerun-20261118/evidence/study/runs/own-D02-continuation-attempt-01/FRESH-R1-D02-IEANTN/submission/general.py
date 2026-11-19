"""Certify high-order Ramanujan profiles on rays; input order defaults below."""
from verify import I,D,ED,fac,comb
from fractions import Fraction
import sys
def cert(n):
    assert n>=4
    m=n+2; b=2*(m+2)
    C=[sum(fac(k)*comb(j,k) for k in range(min(j,m)+1))-
        sum(fac(k)*fac(j-k) for k in range(max(0,j-m),min(j,m)+1))
        for j in range(2*m+1)]
    assert C[:4]==[0,0,0,0] and min(C[4:m+1])>0
    a=max(101,8*(n+3)+2,b+1)
    while True:
        L=I(a); z=L-1
        em=ED(z)+3*z*(b-z).exp()+2*fac(m+1)/z**(m+1)
        coeff=L/z+2*sum(fac(j)/L**j for j in range(m+1))+em
        if (coeff.b<D('3.1') and (I('3.1')*L**(n+1)*em).b<C[n+1]
          and sum(Fraction(max(0,-C[j]),a**(j-m)) for j in range(m+1,2*m+1))<=C[m]):
            print('general tail',n,a); return a
        a+=1
if __name__=='__main__':
    for n in (map(int,sys.argv[1:]) if len(sys.argv)>1 else [20,24,32,48,64]):
        cert(n)
