from cert import I,F,S,f,exp,ln,PI,a,qe,powth
def ck(x,b):assert I(x).below(b),(str(x),str(b))
def cl(x,b):assert I(x).above(b),(str(x),str(b))
rows=[('.78','.80','7.798','4.101'),('.80','.82','8.162','3.694'),
      ('.82','.84','8.928','3.534'),('.84','.86','9.747','3.373'),
      ('.86','.87','10.620','3.213'),('.87','.875','11.076','3.133')]
def W(s,y,c,d):
 s=I(s);q=5-2*s;alpha=(8*s-5)/3
 return 2*(I(c)*exp(q*ln(y)-alpha*y)/(alpha-q/y)+I(d)*exp(-y)*(y*y+2*y+2))
def zc(v):
 return I('.010445')*v/(v-92)+W('.78',ln(3*10**12),'7.798','4.101')*exp(-3*v/40)
def dc(v):
 y=v/3
 T=sum(W(s,y,c,d)*exp((I(b)-I('.875'))*v) for s,b,c,d in rows)
 return I('.018')*v*v*exp(-3*v/8)+I('.009')*v*v*exp(-I('.095')*v)+I('2.091')*v*exp(-5*v/24)+T+I('1.000000147')*exp(-3*v/8)+I('1.78')*exp(-13*v/24)
def w(v):return (1+1/v)/v
def basics():
 # Constants for all-total reciprocal-ordinate bound from FKS 2.3.
 u=ln(100);z=ln(2*PI)
 ell=1/(2*PI)+(I('.137')*u+I('.443'))/(100*u*(u-z))
 R=I('.137')*u+I('.443')*ln(u)+I('1.588')
 ck(ell,'.160');cl(z,'1.83');ck(2*I('.5922435112')+4*R/100,'1.40')
 cl(u/2-z,0)
 b=I('58')
 ck( -I('5.4')*b+I('2.7')**2-4+8*PI*I('1.01')+I('.08')*b*b,0)
 cl(2*ln(34/(PI*exp(1))), '2.7')
 cl(2000-598/ln(2)**2-10,0)
 # proof of CH2 round-ups and onset checks
 ck(PI/(3*10**12),'1.048e-12'); ck(exp(I('29.9')),10**13)
 ck(exp(I('19.3')),250000000);cl(exp(I('19.3')),10**4)
 ck(I('1.751000147')+I('1.78')*exp(-I(F(193,60))),'1.83')
 print('FKS total count, CH2 and integration checks: OK')

def joins():
 b=I('29.9'); m=I(58); L0=F('19.3')
 # Upper bound for integral of either absolute error after 58.
 tb=I('2.1e-10')
 ck(a*(200-58)+230*exp(-29)+I('.16')*exp(-25),'2.1e-10')
 # B is an upper bound after b; the kernel w is decreasing.
 B=2*(b*b+4*b+8)*exp(-b/2)/(8*PI)+tb
 # For [19.3,b], use signed small-x CH2 theta near x.
 # sup over interval with increasing L^j and decreasing endpoint expressions.
 l=L0
 while l<F('29.9'):
  u=min(l+F(1,50),F('29.9')); t=I(l);v=I(u)
  r=exp(-t/2); T=B-I('3.66')*exp(-b/2)
  up=I('3.4511')*r+T
  dn=I('1.83')*r+B
  ck(up*v*v,'.1');ck(dn*v*v,'.1')
  hup=(I('3.4511')+I('3.66')/t)*r/t+w(b)*B
  hdn=I('1.83')*r/t+w(b)*B+2/(t*(exp(t)-1))
  for q in (hup,hdn):
   ck((v**3+I('.1'))*q,'.1')
  l=u
 # b..58 (main normalized terms decrease), then 58..200.
 ck(b*b*(3*b*b+8*b+16)*exp(-b/2)/(8*PI)+m*m*tb,'.1')
 ck((b**3+I('.1'))*((3*b+6)*exp(-b/2)/(8*PI)+2/(b*(exp(b)-1)))+(m**3+I('.1'))*w(m)*tb,'.1')
 ck(200**2*(a+115*exp(-29)+tb),'.1')
 ck((200**3+I('.1'))*((a+115*exp(-29))/58+w(m)*tb+2/(m*(exp(m)-1))),'.1')
 # 200..infinity. Drop exponentials of faster rate for the product tail.
 t=I(200); r=exp(-t/8)
 ck(I('.18')*r*t*t,'.1')
 ck((t**3+I('.1'))*((I('.18')+I('.16')/t)*r/t+2/(t*(exp(t)-1))),'.1')
 print('Mertens all-ray .10 polynomial joins: OK')

def powers():
 # normalized bound for reciprocal and product log errors + H.
 for v,c in [(130,'.065'),(150,'.031'),(175,'.023'),(190,'.021'),(200,'.0195'),(250,'.0166'),(400,'.0136'),(1000,'.01151'),(5000,'.01065'),(20000,'.0105')]:
  t=I(v); r=exp(-t/8); Z=zc(t)
  d=dc(t)
  # 2/(e^t-1) rescaled by exp(t/8) is at most 3 exp(-7t/8).
  bs=(1+I(F(2,3*10**12)))*Z+9*d
  bh=(1+I(F(2,3*10**12))*(1+1/t))*Z+(9+8/t)*d+3*exp(-7*t/8)
  ck(bs,c);ck(bh/(1-bh*r/t),c)
  print('spectral coefficient',v,c, 'checked')
 # Weighted CH2 plateaux with powers removed.
 t=I(100);r=exp(-t/2)
 B=I('1.000100294')*r+I('2.67')*exp(-2*t/3)
 ck(a+I('113.67')*r+B,'1.05e-12')
 coef=2*(a+I('113.67')*r)+B
 ck(coef/(1-coef/t),'2.10e-12')
 print('CH2 weighted plateau and strict spectral improvements: OK')

def constants():
 N=10**7
 t=ln(N); eps=I('.2')/t**2
 # Main integral ∫ dt/(t² log t) = e^-t ∫_0^∞ e^-u/(t+u) du.
 # alternating expansion at m=10, next term bounds the remainder
 J=sum(((-1)**j*f(j)/t**(j+1) for j in range(11)),I(0))/N
 JM=J-f(11)/(N*t**12)
 EC=eps*(3+1/t)/(2*N*t)
 bc=I(1)/N; eb=3*eps/N
 C0=JM/2-EC; C1=J/2+EC+I(1)/(3*N*N)
 B0=bc-eb; B1=bc+eb+I(4)/(N*(N-1))
 for l,h in [(C0,C1),(B0,B1)]:
  a0=(l.a*(1<<56))//S;b0=-(-h.b*(1<<56)//S)
  print('tail units at 2^56: ',a0,b0)

if __name__=='__main__':
 basics(); joins()
 # Powers with v=100/150 etc should be run as directed intervals, not samples.
 powers(); constants()
