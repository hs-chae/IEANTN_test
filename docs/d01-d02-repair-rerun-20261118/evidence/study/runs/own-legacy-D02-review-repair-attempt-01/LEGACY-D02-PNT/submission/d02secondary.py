"""Outward arithmetic for extra D02 primorial and short intervals."""
from d02screen import *
from d02m import combined

def main():
    prelim()
    for L,C,g,m in [(168,'.256418','.514','.0011'),
                    (180,'.237637','.476','.0007'),
                    (200,'.215402','.432','.0011'),
                    (173,'.248838','.499','.000999'),
                    (185,'.232384','.465','.00023'),
                    (204,'.212','.426','.00069')]:
        t=I(L); c=I(C); g=I(g)
        B=screen(F(L),c=F(7,20))+3*e(-(F(1,2)-a)*t)
        assert B<c
        reserve=g-c*(2+b*g*e(-a*t))
        assert reserve>I(m),(L,reserve,m)
        print('interval length and start',g,L,'lower reserve',reserve)
    for L0,cap,shift,bound in [(169,'.256418','.2565','.513'),
                               (174,'.249','.2491','.4982')]:
        L=I(L0); u=e(-a*L)
        C,D,Q=I(cap),I(shift),I(bound)
        assert combined(F(L0-1))<C
        assert screen(F(L0-1),c=F(7,20))+3*e(-(F(1,2)-a)*I(L0-1))<C
        assert log(1-D*u)>-1
        assert C*(1+D*u)<D
        assert (D+C)/(1-D*u)<Q
        assert Q*e(-I(181)/32)<I('.02635')
    # Correlated short interval with log power 207/20.
    L=I(100000); k=F(207,20)
    z=3*L/8-k*log(L)+log(3)
    assert L/3<z and z<2*L/5 and z>h
    assert k/L<F(1,24) and log(3)<L/40
    assert k*log(L)<3*L/8 and k/L<F(3,8)
    assert sum(I(fac(j)*comb(4,j))*F(9,8)**j for j in range(5))<100
    assert sum(I(fac(j)*comb(4,j))*(9/L)**j for j in range(5))<2
    assert I('.4')**3*3*144<I('27.649')
    low=I('172.8')*(1+L/8)*e((-F(12,5))*log(L))
    high=I('27.648')*(e(-F(17,5)*log(L))+1/(F(128,5)*log(L)))
    d=12*(L*L+2*L+2)*(2+L)*e(-a*L)
    rest=(4*e(1)*((L+1)**2/6+3)+I('8.364')*(L+1)*e(-L/40)+9*e(-L/8))*e(-k*log(L))
    v=2*(low+high+d)+rest
    assert v<I('.19')
    print("D02 secondary: short-interval fractional loss",v)
if __name__=='__main__':main()
