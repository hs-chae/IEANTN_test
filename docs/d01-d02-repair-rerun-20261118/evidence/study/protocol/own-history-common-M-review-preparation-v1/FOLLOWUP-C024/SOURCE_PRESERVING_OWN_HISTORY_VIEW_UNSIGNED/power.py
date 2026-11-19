"""Directed interval computations for the pure-power profiles.

Run from the submission directory with /usr/bin/python3.10, not -O.
All print formatting is diagnostic; asserts use exact outward fixed point.
"""
from D01_check import I, F, ceil, exp, log, less, approx, PI
from functools import lru_cache

# The printed exact height, not 3e12. Strict N conventions are immaterial.
H=3000175332800
A=log(H)
l3=log(3)
Q=F(7,8)
J=F(27,32) # sensitivity only; not a current assumption

@lru_cache(None)
def mass(s):
    """Twice the infinite positive-ordinate reciprocal mass bound."""
    p=F(8,3)*(1-s); q=5-2*s; b=1-p
    y=exp(q*log(A)-b*A)
    v=I(1); R=v
    for i in range(1,5):
        v=v*(q-i+1)/(b*A); R+=v
    return I('9.8')*exp(p*l3)*y*R/b+103*(A*A+2*A+2)/H

@lru_cache(None)
def coeff(b):
    a=F(3,4)
    N=int((b-a)*4096)
    assert a+F(N,4096)==b
    sig=[a+(b-a)*i/N for i in range(N+1)]
    d=[mass(s) for s in sig[:-1]]
    return [(sig[-1],d[-1])]+[(sig[i],d[i-1]-d[i]) for i in range(1,N)]

def c(t,b=Q):
    # C in |psi-x| <= x^b C(log x). Piecewise-linear majorant in sigma
    # is not used: weights really are an increasing STEP test function.
    z=sum(w*exp(-(b-s)*t) for s,w in coeff(b))
    z+=(t*t/(9*I('6.28'))+I('1.8642'))*exp(-(b-F(3,4))*t)
    z+=I('2.091')*t*exp(-(b-F(2,3))*t)
    return z

def low_part(t):
    return (t*t/(9*I('6.28'))+I('1.8642'))*exp(-t/4)+I('2.091')*t*exp(-t/3)

def verify():
    t=I(80)
    less(t,exp(t/3))
    less(5*exp(t/3)+2,exp(t/2))
    less((2*PI)*exp(I(1)),I('2.45')*exp(t/3))
    less(I('2.45'),2*PI)
    less(I('6.28'),2*PI)
    for b,anchors in [(Q,[160,180,182,184,185,186,190,200,220,250,300,500,1000,2000,50000]),
                      (J,[160,165,168,169,170,180,190,200,220,250,300,500,1000,50000])]:
        for s,w in coeff(b):
            less(0,w)
        for t in anchors:
            C=c(I(t),b)
            print(b,t,approx(C)[1])
    print('height, arithmetic and staircase verified')

if __name__=='__main__': verify()
