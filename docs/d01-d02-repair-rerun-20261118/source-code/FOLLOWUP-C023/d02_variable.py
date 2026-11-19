"""Checks for the variable-order bound and correction of one D01 scope."""
from d02_density_new import Q, D,D0,F,J,eu
import d02_ram_new as R
from ram_repair import logb,hi,theta_new, H, V
ROWS=((D,'28',3000),(D,'27.8',6700),(D,'27.7',19000),(D,'27.65',190000),
      (D0,'38',3000),(D0,'37',12000),(D0,'36.9',40000))
def variable():
    A0=Q(3000)
    for d in (D,D0):
        p,w=R.frozen(A0,d)
        u=A0-1
        K=p+R.K*w/u+(Q('1.000000147')+Q('2.515')/u)*eu(-(Q(1,2)-d)*u)
        K+=Q('1.78')*eu(-(Q(2,3)-d)*u)+Q('.074')*u*eu(R.s/2-(1-d)*u)
        assert K<1
    assert 4*eu(-(Q(1,2)-D)*(A0-1))<1
    assert 20/ Q(40)==Q(1,2)
    # Li at half-argument: H_20(v)+V_20(v)<2 for v>=40.
    assert R.H(20,Q(40))+R.V(20,Q(40))<2
    # n<=L/27.65, plus L>=3000, controls H, exp(shift), and upper error.
    assert (1/Q('27.65')+1/A0)/(1-1/A0)<Q(1,27)
    assert 2*Q(27,26)+Q('.01')<Q('2.1')
    assert 2/A0**2+2*eu(-D0*(A0-1))<Q('.01')
    assert 1/(1-1/A0)*eu(D)<Q('1.18')
    assert Q('2.36')+Q('4.2')<7
    assert sum(Q(1,k) for k in (1,1,2,6))-(2+Q(4,40))>Q(1,2)
    assert D-(1+logb(Q('27.6'))[0])/Q('27.6')<0
    for d,c,A in ROWS:
        c,A=Q(c),Q(A)
        gap=d-(1+logb(c)[1])/c
        bound=Q('4.2')*(1/c+1/A)+4/(A*(1-2/c))+7*eu(-gap*A)
        print('variable order',d,c,A,'gap',float(gap),'cost',float(bound),flush=True)
        assert gap>0 and bound<Q(1,4)
def correction():
    L=Q(1000)
    # The reviewed shorter Ramanujan error branch is B0.
    def h(t):return hi(t,theta_new(t))
    upper=L**4*(L/(L-1)*(H(L-1)+V(L-1)+h(L-1))-(H(L)-h(L))**2)
    assert H(L)-h(L)>0 and upper<Q('1.015')
    print('B0 counterexample to inherited 1.03 whole ray, L=1000; upper',float(upper))
    assert 1+Q(14,221)+Q(16,221**2)>Q('1.03')
    assert 1+Q(14,476)+Q(145,476**2)>Q('1.03')
    # D02 full degree 4 gives an even better valid finite right endpoint.
    C=R.polys(20)[0]
    e=Q('477.005')
    print('constant 1.03 finite right check',float(sum(C[k]/e**(k-4) for k in range(4,9))))
    assert sum(C[k]/e**(k-4) for k in range(4,9))>Q('1.03')
if __name__=='__main__':
    variable()
    correction()
