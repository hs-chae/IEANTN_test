"""Exact rational certificates supplementing analytic.py, for smoothing and Mertens."""
from analytic import Q, eu, el, logb, pl, pu, c, q, E1, H, V, S, E, h0, m0, mainlower
from functools import lru_cache
from math import factorial, comb

Z=Q(3*10**12)
dd0=Q(1,8)
dd1=Q(5,32)
a=Q('29.9')
zq=Q('3.6e-6')
def point_smooth(L,delta):
    return 119*eu(-L/2)+zq*eu(-delta*L/2)+2*eu(-L)
def pri_smooth(L,delta):
    return ((123*eu(-L/2)*(1+Q(20,9)/L))
            +zq*eu(-delta*L/2)*(1+1/(L*(Q(19,20)-delta/2)))
            +Q(16,5)*L*eu(20-L))
def gd(L,delta):
    return Q('.15916')*((delta*L+Q('3.22'))**2-Q('26.89')**2)+Q('3.7284')+Q('2.091')*L/64
def g_tests():
    lH,uH=logb(Z)
    lH2,uH2=logb(Z/(2*pu))[0],logb(Z/(2*pl))[1]
    rH=Q(1,5)*uH+2
    assert 2/(14*pl)*(logb(14/(2*pl))[1]+1)<Q('.083')
    assert (uH2+3)/(pl*Z)+2*rH/Z**2<Q('3.2e-12')
    assert (uH2+1)/(pl*Z)+(4*rH+Q('.2'))/Z**2<Q('2.961e-12')
    assert uH2**2/(2*pl)+Q('1.8642')<118
    assert lH2>Q('26.89') and logb(Q('2.45')*64/(2*pl))[1]<Q('3.22')
    assert 1/(2*pl)<Q('.15916')
    assert all(gd(Q(200),de)>0 for de in (dd0,dd1))
    # 0.004*L² dominates p_delta(L) even after replacing constant by +1.
    L=Q(1);d=dd1
    qa=Q('.004')-Q('.15916')*d*d
    qb=Q('.15916')*2*d*Q('3.22')+Q('2.091')/64
    qc=gd(Q(0),d)+1
    assert qa>0 and qb*qb+4*qa*qc<0 and 118*eu(-200*(Q(1,2)-d))<1

def m_anchor():
    assert eu(a)<10**13
    assert el(Q(18))>10**7
    # |theta(t)/t-1| < .001 for t >= 10^7, by the two branches in the text.
    assert Q('.751')+Q('1.000000147')+Q('1.78')*eu(-logb(Q(10**7))[0]/6)<2
    assert Q('.001')**2*10**7>4
    assert q+117*eu(-logb(Q(10**13))[0]/2)<Q('.001')
    N=Q(10**7);l,u=logb(N)
    # prime-square reciprocal sum differs from integral I by
    # at most .001*(3+1/logN)/(N logN). Tail k>=3 is <=1/(2N²).
    s=Q('.0031')/(N*l)
    assert ((1-1/l)/(N*u)-s)/2 > Q('2.89e-9')
    assert ((1-1/u+2/l**2)/(N*l)+s)/2+1/(2*N**2)<Q('2.96e-9')

# D1 absolute cap, including elementary prime tail for products.
# For the infinite region use the unconditionally smoothed point bound.
al=Q('1.47e-7')
ep=Q('0.0001')
et=Q('1.78')
z=Q('3.3e-12')
def m_values(L,point,delta=dd0):
    E=eu(-L/2);J=eu(-2*L/3);X=eu(-L);K=eu(-delta*L)
    w=(L+1)/L**2
    integ=w*(Q('.085')*E+z*K+2*X)
    return ((point+(1+al+ep)*E+et*J)/L+integ+
             w*(2*(al+ep)*E+Q(3,2)*et*J)+X)
def m_point(L,mode):
    if mode==0:return Q('.791')*eu(-L/2)
    if mode==1:return c*L*L*eu(-L/2)
    return point_smooth(L,dd0)
def m_ray():
    # On each of these branches L^3 * m_values is decreasing:
    # terms are nonnegative sums of polynomials of degree <=4 times
    # decaying exponentials, starting to the right of each maximum.
    for k,L in [(Q('.10'),Q(18)),(Q('.06'),Q(19)),(Q('.05'),Q('19.5')),
                (Q('.03'),Q(21)),(Q('.011'),Q(23))]:
        for b,mode in [(L,0),(a,1),(Q(58),2)]:
            u=m_values(b,m_point(b,mode))
            assert b**3*u/(1-u)<k,(k,b)
    # Certified analytic/finite link endpoints.
    assert eu(Q(18))<10**8 and eu(Q(19))<1500000000
    assert eu(Q('19.5'))<2500000000 and eu(Q(21))<10**10
    assert eu(Q(23))<10**10
def m_positive():
    # Divide the lower Dlog by exp(-L/2)/L. Use separate monotone
    # endpoints for the exponential-tail terms with opposite signs.
    L=Q(20); U=a
    LO=L/(L+2)
    cost=(Q('.751')+al+et*eu(-L/6)+(1+1/L)*
          (Q('.085')+2*ep+z*eu((Q(1,2)-dd0)*U)+2*eu(-L/2))
          +L*eu(-L/2))
    assert LO-cost>Q('.003')
    cost2=(Q('.751')+al+et*eu(-L/6)+Q('.083')+2*ep+
           Q('3.2e-12')*eu((Q(1,2)-dd0)*U)+2*eu(-L/2))
    assert 1-cost2>Q('.10')

def R_margin():
    # These are independent of density estimates.
    for de,n in [(dd0,Q(12)),(dd1,Q('13.9'))]:
        for j in range(480,3000):
            x=Q(j,10);y=x+Q(1,10)
            if j%10 and (j<465 or j>=2700):continue
            if j>=2700:y=x+1
            def err(t,w):
                b=[pri_smooth(t,de),h0(t)+m0(t)]
                if w<=58:b.append(c*t*t*eu(-t/2))
                if de==dd1 and t>=220:b.append(E1(t))
                return min(b)
            s=V(x)+err(x,y)
            sh=y**4*x/(x-1)*err(x-1,y-1)
            # For the first few bins a directly decreasing Schoenfeld branch
            # can be sharper than freezing the log power at the right.
            if y-1<=58:
                sh=min(sh,c*x**5*(x-1)*eu(-(x-1)/2))
            # The -n/y combines with the positive c5=14 in mainlower.
            assert mainlower(x,y)-n/y-sh-y**4*s*(2*H(x)+s)>1,(de,n,x,y)
        x=Q(300)
        v=V(x)+pri_smooth(x,de)
        assert x**5*(x/(x-1)*pri_smooth(x-1,de)+v*(2*H(x)+v))<14-n
        assert sum(Q(S[k])*x**(6-k) for k in range(21,41))<145

if __name__=='__main__':
    g_tests();m_anchor();m_ray();m_positive();R_margin()
    print('signed-tail, smoothing, and extended-margin certificates OK')
