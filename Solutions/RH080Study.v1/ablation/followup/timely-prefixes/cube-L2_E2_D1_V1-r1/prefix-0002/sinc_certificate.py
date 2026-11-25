"""Exact scalar caps for the log-trapezoid under BPT. Python 3.10 stdlib only.
Not a program-verification claim. All positive constants in cap() are rational.
"""
from fractions import Fraction as Q
from functools import lru_cache

SCALE = 10**10
P, PHI = Q("3.14159"), Q("3.14160")

def upward(x):
    return -((-x.numerator*SCALE)//x.denominator)

def logarithm01(n,d):
    """Lower and upper bounds for log(n/d), 1 <= n/d <= 2."""
    assert d <= n <= 2*d
    r = Q(n-d,n+d)
    a = r
    lo = 0
    for j in range(12):
        lo += 2*a/(2*j+1)
        a *= r*r
    return lo,lo+2*a/(25*(1-r*r))

L2,H2 = logarithm01(2,1)
L2 = Q(L2.numerator*SCALE//L2.denominator,SCALE)
H2 = Q(upward(H2),SCALE)

def loghi(n,d=1):
    """Integer upper bound in SCALE units for log(n/d)."""
    v = n.bit_length()-d.bit_length()
    if v >= 0:
        d <<= v
    else:
        n <<= -v
    if n < d:
        n <<= 1
        v -= 1
    # use the rounded upper bound after monotone rational evaluation
    return upward(logarithm01(n,d)[1] + v*(H2 if v>=0 else L2))

@lru_cache(None)
def sin_unit(j,D):
    """Absolute sine of pi*j/D, upper bound after reduction to [0,pi/2]."""
    assert 0 <= 2*j <= D
    a,b = P*Q(j,D), PHI*Q(j,D)
    return Q(upward(min(Q(1),b-a**3/6+b**5/120-a**7/5040+b**9/362880)),SCALE)

def sinhi(j,D):
    t=j%D
    return sin_unit(min(t,D-t),D)

def certificate(K,M,J,offset):
    """Return A,B,V,C: signed zero bound / sqrt(x) <= A*L+B+
    (42/25)*(L+C)*V/n. J means upper endpoint index (u_J=pi*J/M).
    """
    j0=(M*100000+314158)//314159
    assert j0*P>=M
    d1=PHI/(2*M)
    d2=d1/K
    acc=0
    acc_log=0
    tv=0
    prev=SCALE
    for j in range(j0,J):
        ulo=P*Q(j,M)
        s=sinhi(2*j+1,2*M)
        t=sinhi(2*j+1,2*M*K)
        h1=min(Q(1),(s+d1)/ulo)
        h2=min(Q(1),K*(t+d2)/ulo)
        u=upward(h1*h2)
        tv+=abs(prev-u)
        prev=u
        acc+=u
        acc_log+=u*loghi(j+1,2*M)
    tv+=prev
    tail=2*K/(P*P*Q(J,M))
    A=2*Q(j0,M)+2*Q(acc,M*SCALE)+tail
    B=A*offset+2*Q(j0,M)*(Q(loghi(j0,2*M),SCALE)-1)
    B+=2*Q(acc_log,M*SCALE*SCALE)
    B+=tail*(Q(loghi(J,2*M),SCALE)+1)
    # |R| <= .28 log(Tu); 2h <= 6/n, hence factor 1.68/n.
    C=offset+Q(loghi(4*J,M),SCALE)
    V=Q(tv,SCALE)+3*K/(P*Q(J,M))**2  # includes tail residual, log(T*uJ)>=.5
    assert 0 < A and 0 < C and 0 < V
    return A,B,V,C

def cap(K,M,J,offset,loL,hiL,sqrta,a,c, printed):
    # 3/ n >= H >= 3/(n+1), and T=2/h, h=H*K/(K+1).
    # ln(T/n) <= log(2*(K+1)*(a+1)/(3*K*a)).
    assert Q(loghi(2*(K+1)*(a+1),3*K*a),SCALE) < offset
    A,B,V,C=certificate(K,M,J,offset)
    A0,B0,V0,C0=printed
    assert A<=A0 and B<=B0 and V<=V0 and C<=C0
    A,B,V,C=printed
    assert loL>=8 and loL<=hiL and sqrta>0 and a>=2980
    assert A*(loL-2)+B>=0 and A*loL+B>=0 and C>0
    main=Q(K,K+1)*Q(a,a+1)*1/(1+1/(a*loL))
    zero=(A*hiL+B+Q(42,25)*(hiL+C)*V/a+Q(21,4*a))/(3*sqrta)
    powers=2*hiL/(a*sqrta)+4*hiL**2/a**2
    trivial=Q(1,3*a**5)
    assert main-zero-powers-trivial>c, (float(main),float(zero),float(powers))
    print("K,M,J, target =", K,M,J,c, "certified scalar caps =", printed,
          "bound", float(main-zero-powers-trivial))

if __name__=="__main__":
    cap(32,64,64*256,Q("-.37"),Q(8),Q(8),Q("54.598"),2980,Q(".8591"),
        tuple(map(Q,("2.528","-2.218","2.841","6.562"))))
    cap(480,96,96*2048,Q("-.4"),Q("14.58"),Q("14.583039"),Q("1467.798"),
        2154433,Q(".9855"),tuple(map(Q,("3.635","1.526","4.536","8.611"))))
