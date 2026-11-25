"""Exact rational finite-grid notch coefficients (no prime or zero samples)."""
from fractions import Fraction as Q
import sys
sys.dont_write_bytecode = True
from scalars import exp_bounds, pl, pu, m, T, s

# We use a tighter upper pi bound for finding dist to k*pi. Mathlib pi_lt_d6.
pu = Q('3.141593')
assert exp_bounds(Q('.693147'))[1]<2<exp_bounds(Q('.693148'))[0]
assert (T+8)/s<Q(1,50)
r=Q(3,997)

def sup_ratio(a,b):
    if b<=1:
        return 1-a*a/6+a**4/120
    k = int((a+b)/(pu+pl)+Q(1,2))
    d = max(abs(a-k*pl),abs(a-k*pu),abs(b-k*pl),abs(b-k*pu))
    if 2*d>=pl:
        return Q(1)
    q=(d-d**3/6+d**5/120)/min(1,a)
    return min(1,q)

def log_lower(a):
    k=a.numerator.bit_length()-a.denominator.bit_length()
    w=a/Q(2)**k
    if w<1: k-=1;w*=2
    assert 1<=w<2
    return k*Q('.693147' if k>=0 else '.693148')+2*(w-1)/(w+1)

def down(x,z=10**12):
    return Q(x*z//1,z)

step=Q(1,10)
alpha,beta=Q(0),Q(0)
S=Q(0)
for i in range(1,12000):
    a,b=i*step,(i+1)*step
    w=(1-sup_ratio(a,b)*sup_ratio(r*a,r*b))*min(1,1/b)*min(1,1/(r*b))
    # Controlled rounding yields lower coefficients and a separate upper error sum.
    alpha += down(w*step*Q('.636'))
    beta += down(w*step*Q('.636')*(log_lower(a)-Q('2.25')))
    S += down(w)+Q(1,10**12)

g=Q('5.81')
C=Q('.637')*(2+g)-alpha
Dc=Q('.637')*(g+g*g/2+Q('.00001')-(2+g)*Q('2.239'))-beta
# All BPT endpoints used in the notch estimate have T in [x0, exp(t+8)].
assert step*m/Q('1.5')>2*pu
E=(Q('1.68')+Q('3.36')*S+9)/(50*s)+Q('.000001')
R=(Q('.997')*(1-1/m)-(C*T+Dc+E)/(3*s))*(1-1/(14*m))
assert C>0 and 12*C+Dc+E>0
print('gain alpha,beta, endpoint mass and final certified lower (rounded down):')
print(*(str(down(z,10**6)) for z in (alpha,beta,S,R)))

assert R > Q('.9848')
assert (1-Q('.9848'))**2*1737 > Q(19,30)**2
