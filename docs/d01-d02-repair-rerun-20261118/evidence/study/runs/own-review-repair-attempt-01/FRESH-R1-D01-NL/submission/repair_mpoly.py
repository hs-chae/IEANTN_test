from mcert import I,F,S,exp,PI,a,ck,w
def joins(L0,c):
 c=I(c)
 L0=F(L0)
 assert exp(I(L0)).below(4000000000) and L0>=F("19.3")
 b=I('29.9'); m=I(58)
 # Upper bound for integral of either absolute error after 58.
 tb=I('2.1e-10')
 ck(a*(200-58)+230*exp(-29)+I('.16')*exp(-25),'2.1e-10')
 # B is an upper bound after b; the kernel w is decreasing.
 B=2*(b*b+4*b+8)*exp(-b/2)/(8*PI)+tb
 # For [L0,b], use signed small-x CH2 theta near x.
 # sup over interval with increasing L^j and decreasing endpoint expressions.
 l=L0
 while l<F('29.9'):
  u=min(l+F(1,50),F('29.9')); t=I(l);v=I(u)
  r=exp(-t/2); T=B-I('3.66')*exp(-b/2)
  up=I('3.4511')*r+T
  dn=I('1.83')*r+B
  ck(up*v*v,F(c.a,S));ck(dn*v*v,F(c.a,S))
  hup=(I('3.4511')+I('3.66')/t)*r/t+w(b)*B
  hdn=I('1.83')*r/t+w(b)*B+2/(t*(exp(t)-1))
  for q in (hup,hdn):
   ck((v**3+c)*q,F(c.a,S))
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


if __name__=="__main__":
 joins("22.1",".0391")
