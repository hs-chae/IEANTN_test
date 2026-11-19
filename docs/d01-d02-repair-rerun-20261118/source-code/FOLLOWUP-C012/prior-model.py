from interval import *
from math import comb, factorial
Q=Fraction
PI8=Q("25.1327412")
B0=Q(7,8); B1=Q(27,32); A=58; H=3*10**12
h=ln(H)
def coefficient(s):
 p=8*(1-s)/3
 q=5-2*s
 a=1-p
 # q<4; log(log H) enclosed via simple fixed rational endpoints
 lh=I(ln(Q(h.a,S)).a,ln(Q(h.b,S)).b,True)
 assert (h-I('28.72963')).yes() and (I('28.72964')-h).yes()
 return 2*(I('4.9')*exp(p*ln(3)+q*lh-a*h)/(a-q/h)+I('51.5')*(h*h+2*h+2)/H)
def spectral(beta,start=Q('.77'),step=Q('.001')):
 s=start; xs=[s]
 while s+step<beta:s+=step;xs.append(s)
 cs=[coefficient(x) for x in xs]+[I(0)]
 c=[(cs[j]-cs[j+1],0,1-y) for j,y in enumerate(xs[1:]+[beta])]
 assert all(t[0].yes() for t in c)
 return [(I(2),0,Q(1,2)),(I(13),1,Q(1,2)),(I(1)/24,2,Q(1,2)),(I(1),0,1-start),(I(1)/48,2,1-start)]+c
# Multiple alternative bin cutoffs retained when useful; margins certify the default .77 branch.
M0=spectral(B0);M1=spectral(B1)
CH=[(I('0.000000000001047198'),0,Q(0)),(I('113.67'),0,Q(1,2))]
POWER=[(I('1.000000147'),0,Q(1,2)),(I('1.78'),0,Q(2,3))]
@lru_cache(maxsize=None)
def weight(L,d,a):
 return ex(-a*L)*L**d
def mix(L,m):
 return sum(c*weight(L,d,a) for c,d,a in m)
def shifted(L,m,a):
 return sum(c*weight(L,d,b-a) for c,d,b in m)
@lru_cache(maxsize=None)
def pe(L,method):
 if method==-1:
  return weight(L,2,Q(1,2))/PI8
 m=[CH,M0,M1][method]+POWER
 return sum(c*weight(L,d,a)*(1+1/(L*(1-a-Q(2,A)))) for c,d,a in m)+weight(L,1,Q(1))*ex(Q(A,2))*2*A/PI8
N=12
C=[sum(factorial(j)*comb(k,j) for j in range(min(k+1,N)))-sum(factorial(j)*factorial(k-j) for j in range(max(0,k-N+1),min(N,k+1))) for k in range(2*N-1)]
def f(L):return sum(Q(factorial(j),1)/L**(j+1) for j in range(N))
def hrem(L):return 2*factorial(N)/L**N
def E(L,mode,post=False):
 if L<A or (L==A and not post):return pe(L,-1)
 ans=mn(pe(L,0),pe(L,1))
 return mn(ans,pe(L,2)) if mode==1 else ans
def err(lo,hi,mode):
 def cell(a,b):
  return mx(E(a,mode),E(Q(A),mode,True)) if a<=A<b else E(a,mode)
 v=I(0) if hi<=Q('43.74') else cell(lo,hi)
 w=v+hrem(lo)
 return hi**4*(lo/(lo-1)*cell(lo-1,hi-1)+2*lo*f(lo)*w+w*w)
def lower(lo,hi,mode,k):
 # Scaled profile subtracting the first k leading coefficients.
 assert k<=10
 return sum((Q(c)* (hi if c>0 else lo)**(k+4-i)) for i,c in enumerate(C)
    if i>=4+k and c)-hi**k*err(lo,hi,mode)
def tail_err(L,mode,k):
 # choose a single decaying bound in place of the pointwise minimum.
 assert L-1>=75 and k<=10
 u=pe(L,mode+1)+hrem(L)
 return L**(k+4)*(L/(L-1)*pe(L-1,mode+1)+2*L*f(L)*u+u*u)
