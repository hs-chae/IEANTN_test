from mcert import I,F,S,exp,PI,a,ck,w
from functools import lru_cache
from early2 import ca
@lru_cache(None)
def tails():
 ans=[]
 for positive in (False,True):
  z=I('2.1e-10');h=z*w(I(58))
  for L,R in [(F('29.933'),F('33.3')),(F('33.3'),F(58))]:
   l=L
   while l<R:
    u=min(l+F(1,50),R)
    v=ca(l,u,positive)*exp(-I(l)/2)*(u-l)
    z+=v;h+=v*w(I(l))
    l=u
  ans.append((z,h))
 return ans
def joins(L0,c):
 c=I(c)
 L0=F(L0)
 assert exp(I(L0)).below(4000000000) and L0>=F("19.3")
 b=I('29.933'); m=I(58)
 assert exp(b).below(10**13)
 # Upper bound for integral of either absolute error after 58.
 tb=I('2.1e-10')
 ck(a*(200-58)+230*exp(-29)+I('.16')*exp(-25),'2.1e-10')
 # B is an upper bound after b; the kernel w is decreasing.
 B=2*(b*b+4*b+8)*exp(-b/2)/(8*PI)+tb
 # Lower theta error uses the actual powers, rather than freezing 1.83.
 A=I('1.751000147');Q=I('1.78');D=I('.2089')
 b1=exp(-b/2);b2=exp(-2*b/3)
 (Tminus,Hminus),(Tplus,Hplus)=tails()
 k=F(1,1000);l=L0
 while l<F('29.933'):
  u=min(l+k,F('29.933'));t=I(l,u)
  r=exp(-t/2);s=exp(-2*t/3)
  intr=2*A*(r-b1)+3*Q/2*(s-b2)
  # tail sign is not known, so use both signed upper envelopes.
  pos=-D*r+intr+Tminus
  neg=A*r+Q*s-2*D*(r-b1)+Tplus
  ck(pos*t*t,F(c.a,S));ck(neg*t*t,F(c.a,S))
  pos1=-D*r+(1+1/t)*intr+t*Hminus
  neg1=A*r+Q*s-2*t*w(b)*D*(r-b1)+t*Hplus
  neg1+=2/(exp(t)-1)
  for d in (pos1,neg1):
   ck((t*t+c/t)*d,F(c.a,S))
  l=u
 # b..58 (main normalized terms decrease), then 58..200.
 ck(b*b*(3*b*b+8*b+16)*exp(-b/2)/(8*PI)+m*m*tb,F(c.a,S))
 ck((b**3+c)*((3*b+6)*exp(-b/2)/(8*PI)+2/(b*(exp(b)-1)))+(m**3+c)*w(m)*tb,F(c.a,S))
 ck(200**2*(a+115*exp(-29)+tb),F(c.a,S))
 ck((200**3+c)*((a+115*exp(-29))/58+w(m)*tb+2/(m*(exp(m)-1))),F(c.a,S))
 # 200..infinity. Drop exponentials of faster rate for the product tail.
 t=I(200); r=exp(-t/8)
 ck(I('.18')*r*t*t,F(c.a,S))
 ck((t**3+c)*((I('.18')+I('.16')/t)*r/t+2/(t*(exp(t)-1))),F(c.a,S))
 print('New Mertens all-ray polynomial join:',L0,c,flush=True)


if __name__=='__main__':
 from early2 import test
 test()
 print('signed tail bounds at 29.933 (absolute signed upper enclosures)',*(str(x) for pair in tails() for x in pair),flush=True)
 import sys
 for c in sys.argv[1:] or ('.0375','.0378','.038','.0381','.0382','.0383','.0385','.039'):
  try:joins('22.109',c)
  except AssertionError as e:print('not certified',c,e,flush=True)
