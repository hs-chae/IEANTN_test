"""Exact rational checks for the Mertens joins and simplified exponential tails."""
from certify import F, E, EP, ex, g, CH, P, DEN
J0=F('29.9')
sign=F('39.47')
assert EP(J0)<10**13
assert EP(sign)<139*10**15
assert EP(20)<500000000<1/E(F("20.1"))
# K bounds the relative theta error times exp(L/8). All terms decrease for L>=150.
def K(L):
 return (F('.01058')*L/(L-F('91.2'))+F('.018')*L**2*E(3*L/40)
         +F('2.091')*L*E(5*L/24)
         +sum(b*E((c-F(1,8))*L) for b,m,c in P))
K200=K(F(200))
assert K200<F('.022')
assert K(F(400))<F('.015')
assert K(F(810))<F('.013')
def a(L):return F('1.752')*E(L/2)+F('1.78')*E(2*L/3)
def fint(L):return 2*(L*L+4*L+8)*E(L/2)/25
def binteg(L):
 h=max(L,F(58)); ans=8*K200*E(25)+CH[0][0]*(200-h)
 for b,m,c in CH[1:]+P:ans+=b*E(c*h)/c
 if L<58:ans+=fint(max(L,J0))
 if L<J0:
  for b,c in [(F('1.752'),F(1,2)),(F('1.78'),F(2,3))]:
   ans+=b/c*(E(c*L)-ex(c*J0)[0])
 return ans
def bpoint(L):
 if L<J0:return a(L)
 if L<58:return L**2*E(L/2)/25
 return g(L,CH+P)
def join():
 Cw=Cp=Cs=F(0)
 for start,end in [(F(20),J0),(J0,sign),(sign,F(58)),(F(58),F(200))]:
  l=start
  while l<end:
   h=min(l+F(1,20),end)
   b=bpoint(l);v=binteg(l)
   w=max(v,b+binteg(sign)) if h<=sign else b+v
   s=w*(1+1/l)/l
   raw=s+E(l)/(2*(1-E(l)))
   Cw=max(Cw,w*h**2)
   Cs=max(Cs,s*h**3)
   Cp=max(Cp,raw/(1-raw)*h**3)
   l=h
 assert max(Cp,Cs,Cw)<F('.08')
 print('join ceilings x 10^6',*[(-(-v*10**6).__floor__()) for v in (Cs,Cp,Cw)])
 # At L=200 onward take v=Kt(L)e^(-L/8). Each of the normalized
 # upper envelopes decreases, by differentiating each constituent.
 L=F(200);v=K200*E(L/8)
 d=E(L)/(2*(1-E(L)))
 raw=(9+8/L)*v/L+d
 assert max(9*v*L**2,raw/(1-raw)*L**3)<F('.08')
 for J,k in [(200,F('.022')),(400,F('.015')),(810,F('.013'))]:
  L=F(J)
  # dominate Dtail after scaling by exp(L/8)*L (decreasing from J)
  c=(9+8/L)*k+L*E(7*L/8)/(2*(1-E(L)))
  assert c/(1-c*E(L/8)/L)<9*k+F('.001') if J>=400 else c/(1-c*E(L/8)/L)<F('.199')
  print('exponential',J,str(9*k),str(9*k+F('.001') if J>=400 else F('.199')))
def Kt(L):
 m1,m2,d=F('91.2'),F('88.9'),F('.02')
 return (K(L)-F('.01058')*L/(L-m1)+F('.01058')*(L/(L-m2)
         +(m1-m2)*L/((L-m1)*(L-m2))*E(d*(L-m2))))
def osc(J):
 L=F(J);m=2*L/5+1
 # K may include the tiny theta prime-power correction, which is safe.
 v=Kt(L)
 strip=40*m**4*E(14*L/75)+8*m**2*E(2*L/5)
 ierr=(2*(v+F('.008')*L**2*E(3*L/40))/(3*10**12)+F('.104')*L**2*E(3*L/8)
       +F('.7')*L*E(3*L/40)+8*strip
       +F('3.1365')*L**2*E(11*L/40)+8*Kt(2*L)*E(L/8))
 powers=F('1.000102')*E(3*L/8)+F('2.67')*E(13*L/24)
 w=v+ierr+powers
 d=w+ierr/L
 return w,d/(1-d*E(L/8)/L)
def runosc():
 for J,cw,cd in [(150,'.036','.036'),(182,'.02164','.02164'),
                  (190,'.02046','.02046'),(194,'.020','.020'),
                  (195,'.019865','.019865'),(200,'.019354','.019354'),
                  (250,'.016438','.016438'),(400,'.013604','.013604'),
                  (810,'.011885','.011885'),(1500,'.011247','.011247'),
                  (3000,'.010904','.010904')]:
  w,d=osc(J)
  assert w<F(cw) and d<F(cd),(J,float(w),float(d))
  print('oscillatory',J,cw,cd)
def precise():
 def arint(l,h):
  if l<J0:
   return sum(b/c*(E(c*l)-ex(c*h)[0]) for b,c in [(F('1.752'),F(1,2)),(F('1.78'),F(2,3))])
  if l<58:return fint(l)-2*(h*h+4*h+8)*ex(h/2)[0]/25
  return CH[0][0]*(h-l)+sum(b/c*(E(c*l)-ex(c*h)[0]) for b,_,c in CH[1:]+P)
 def k(L):return (L+1)/L**2
 w=8*K200*E(25); t=k(F(200))*w
 mx=[F(0)]*4
 for left,right in reversed([(F(20),J0),(J0,sign),(sign,F(58)),(F(58),F(200))]):
  h=right
  while h>left:
   l=max(left,h-F(1,10))
   integ=arint(l,h);w+=integ;t+=k(l)*integ
   b=bpoint(l)
   if l==sign:ws,ts=w,t
   neg=b+(ws if h<=sign else w)
   neg1=b/l+(ts if h<=sign else t)
   drop=F('.208')*ex(h/2)[0] if h<=J0 else F(0)
   pos=w-drop+(0 if h<=sign else b)
   pos1=t-drop/h+(0 if h<=sign else b/l)
   d=E(l)/(2*(1-E(l)))
   mn=neg1+d
   caps=(max(neg1,pos1)*h**3,max(mn/(1-mn),pos1)*h**3,
         max(pos1/(1-pos1),mn)*h**3,max(neg,pos)*h**2)
   mx=[max(a,b) for a,b in zip(mx,caps)]
   h=l
 assert max(mx[:3])<F('.0667') and mx[3]<F('.0726')
 assert F('.020')*200**2*E(25)<F('.0667')
 print('refined ceilings x 10^6',*[(-(-v*10**6).__floor__()) for v in mx])
def mid():
 L=F(80);a=CH[0][0];h=CH[1][0]*E(L/2)
 p=F('1.000102')*E(L/2)+F('2.67')*E(2*L/3)
 assert a+h+p<F('1.049e-12')
 d=2*a+h*(1+2/L)+p
 assert d/(1-d/L)<F('2.097e-12')
 print('CH midpoint branch',80,'2.097e-12','1.049e-12')
if __name__=='__main__':join(); runosc(); precise(); mid()
