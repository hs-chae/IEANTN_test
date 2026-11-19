"""Higher Ramanujan orders; exact tail checks and optional finite joins."""
from verify import *
K=20
coeff=[sum(factorial(j)*comb(i,j) for j in range(min(K,i+1)))-
       sum(factorial(j)*factorial(i-j) for j in range(max(0,i-K+1),min(K,i+1)))
       for i in range(2*K-1)]
rr=Q(52)
extra_br=li_anchor(rr)/ex(rr)-sum(Q(factorial(j))/rr**(j+1) for j in range(K))
assert extra_br.yes() and (Q(2*factorial(K))/rr**(K+1)-extra_br).yes()
assert sum(Q(factorial(j),factorial(N))/rr**(j-N) for j in range(N,K))+Q(2*factorial(K),factorial(N))/rr**(K-N)<2
RSP=[spectral(b,tighter=True) for b in (B0,B1)]
@lru_cache(maxsize=None)
def P(u,b):
 m=RSP[b]+POWER
 return sum(c*weight(u,d,a)*(1+1/(u*(1-a-Q(2,A)))) for c,d,a in m)+weight(u,1,Q(1))*ex(Q(A,2))*2*A/PI8
def F(u):
 return sum(Q(factorial(j),1)/u**(j+1) for j in range(K))
def hh(u):return Q(2*factorial(K),1)/u**K
def tail(L,b,k):
 assert L>=250 and k+4<K
 assert Q(k+4)/L+Q(2)/(L-1)<Q(1,8)
 u=P(L,b)+hh(L)
 e=L**(k+4)*(L/(L-1)*P(L-1,b)+2*L*F(L)*u+u*u)
 return coeff[4+k]+sum(Q(a)*L**(k+4-i) for i,a in enumerate(coeff) if i>4+k and a<0)-e

@lru_cache(maxsize=None)
def p100(u,b):
 assert u>=100
 t=Q(100); a0=Q('.23'); D4=coefficient(Q('.77'),True)
 assert (116-D4).yes()
 assert ((ln(H)-ln(2*Q('3.141594')))**2/(4*Q('3.141594'))-Q('.9321')-55).yes()
 assert Q(200)/(100**2-48*170)<a0
 # All terms except the two near-.77 background terms.
 m=RSP[b][:3]+RSP[b][5:]+POWER
 anch=pe(t,0)+mix(t,CH+POWER)
 r=(u*u/48-54-D4)*ex(-a0*u)
 return (u/t*ex(t-u)*anch+
    r*(1+1/(u*(1-a0)))+
    sum(c*weight(u,d,a)*(1+1/(u*(1-a-Q(2,t)))) for c,d,a in m))

@lru_cache(maxsize=None)
def best(u,b):
 assert u>=59
 ans=mn(P(u,b),E(u,b))
 return mn(ans,p100(u,b)) if u>=100 else ans
def finite(a,z,b,k):
 assert 60<=a<=z and k+4<K
 main=sum(Q(c)*(z if c>0 else a)**(k+4-i) for i,c in enumerate(coeff) if i>=4+k and c)
 w=best(a,b)+hh(a)
 return main-z**(k+4)*(a/(a-1)*best(a-1,b)+2*a*F(a)*w+w*w)

# (order k, c, sufficient log-onset B0, sufficient log-onset B1)
ROWS_H=[
 (6,1500000,348,284),(7,18000000,385,312),(8,200000000,409,329),
 (9,2800000000,446,357),(10,37000000000,478,381),(11,500000000000,510,405),
 (7,19063832,390,315),(8,241691425,426,341),(9,3277187246,462,368),
 (10,47424796805,498,395),(11,730550160076,534,422),
 (12,11946592513217,571,449),(13,206824220948690,607,477),
 (14,3780755108724421,646,506)
]
ROWS_2=[
 (0,60,'19.85'),(1,60,'81.8'),
 (0,202,'120'),(1,175,'120'),
 (0,217,'145'),(1,186,'145'),
]
def check2():
 for b in (0,1):
  r=[(u,Q(c)) for m,u,c in ROWS_2 if m==b]
  assert max(c for u,c in r)==coeff[6]
  assert tail(Q(320),b,3).yes()
  def cell(a,z,c,depth):
   p=finite(a,z,b,2)
   if (p-c).yes():return
   assert depth>0,(a,z,b,c,p)
   m=(a+z)/2
   cell(a,m,c,depth-1);cell(m,z,c,depth-1)
  for j in range(600,3200):
   a,z=Q(j,10),Q(j+1,10)
   cell(a,z,max(c for u,c in r if u<=a),12)
  print('matched order-2 whole rays',b,r,flush=True)

def run():
 for k,c,u0,u1 in ROWS_H:
  for b,u in enumerate((u0,u1)):
   exact=c==coeff[4+k]
   assert (tail(Q(u),b,k+int(exact))-(0 if exact else c)).yes()
  print('higher whole ray',k,c,u0,u1,flush=True)
if __name__=='__main__':run();check2()
