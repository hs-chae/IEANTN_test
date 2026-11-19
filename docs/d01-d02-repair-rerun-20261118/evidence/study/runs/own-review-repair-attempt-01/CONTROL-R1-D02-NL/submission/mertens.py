from model import *
# Simplified analytic branches used to certify constants.  Full envelope in mertens.md
def tail1(L):
  e2=Q('20.83')/(L/2)**3;e3=Q('20.83')/(L/3)**3
  return (1+3*e2)*ex(-L/2)+(2*(1+e3)+(1+5*e3)/2/(1-ex(-L/3)))*ex(-2*L/3)
def J(L,mode,k):
 a=[Q(1,8),Q(5,32)][mode]
 if k==0:return Q('.1')*ex(-L/2)+Q('1e-11')*ex(-a*L)+Q('2.1')*ex(-L)
 return (1/L+1/(L*L))*(Q('.2')*ex(-L/2)+Q('2e-11')*ex(-a*L)+Q('2.1')*ex(-L))
def delta(L,mode,post=False):
 x=mix(L,CH)
 if L<=58:x=mn(x,weight(L,2,Q(1,2))/25)
 if L<Q("29.9") or (L==Q("29.9") and not post):x=mn(x,Q(".791")*ex(-L/2))
 if L>=40:x=mn(x,mix(L,M0 if mode==0 else M1))
 return x
FINE=[spectral(B0,step=Q('.000125')),spectral(B1,step=Q('.000125'))]
def pconst(L,mode,fine=True):
 assert L>=40
 # Scaled envelope for A and H, including the entire raw prime-power tail.
 # Product error <= D exp(D) when |log normalized product| <= D.
 a=[Q(1,8),Q(5,32)][mode]
 m=(FINE if fine else [M0,M1])[mode]
 for c,d,b in m:assert d<=(b-a)*L
 # All scaled terms bounded by their values at L (decreasing polynomial*exponential).
 scale=ex(a*L)
 d=shifted(L,m,a)
 h=d+scale*(J(L,mode,0)+tail1(L))
 p=d+scale*(L*J(L,mode,1)+tail1(L))
 return h,p*(1+2*p*ex(-a*L)/L),p
ROWS=[(0,140,'.020'),(0,170,'.015'),(0,190,'.0132'),(0,225,'.0115'),
 (0,320,'.0095'),(0,450,'.0086'),(0,800,'.0077'),
 (1,140,'.359'),(1,160,'.286'),(1,175,'.254'),(1,200,'.222'),
 (1,250,'.189'),(1,300,'.172'),(1,500,'.146'),(1,1000,'.131')]
LOGS=[
 (0,16,2,'.194','.206'),(0,17,2,'.130','.137'),(0,18,2,'.086','.091'),
 (0,20,2,'.038','.040'),(0,22,2,'.0164','.0174'),(0,24,2,'.0107','.0108'),
 (0,32,2,'.0049','.005'),(0,40,2,'.000216','.000217'),
 (0,40,4,'.348','.349'),(0,55,2,'4.01e-7','4.02e-7'),
 (0,65,2,'3.65e-8','3.65e-8'),(1,65,2,'2.97e-8','2.972e-8'),
 (0,55,4,'.001267','.001268'),(1,55,4,'.001216','.001220'),
 (1,65,4,'.000843','.000843'),(0,55,6,'44.07','44.10'),
 (1,55,6,'23.89','23.90'),(0,200,6,'11.61','11.61'),
 (1,175,6,'10.14','10.15'),(1,200,6,'.397','.397'),
 (0,40,8,'1533000','1534000'),(1,40,8,'898000','901000'),
 (1,55,8,'678000','678000'),(1,175,8,'311000','311000'),
 (1,200,8,'15900','15900')]
def run():
 assert (I(67000000)-ex(18)).yes()
 for b,l,c in ROWS:
  q=pconst(Q(l),b);assert all((Q(c)-x).yes() for x in q),(b,l,c,q)
  print('Mertens',b,l,c,flush=True)
 for mode,on,v,c in [(0,40,Q('186.11'),Q('.01334')),(1,40,Q('168.07'),Q('.2665'))]:
  a=[Q(1,8),Q(5,32)][mode]
  l=Q(on)
  assert all((c-q).yes() for q in pconst(v,mode))
  cap=CH[0][0]*ex(a*v)+(CH[1][0]*ex(-(Q(1,2)-a)*l))
  hh=cap+ex(a*l)*(J(l,mode,0)+tail1(l))
  pp=cap+ex(a*l)*(l*J(l,mode,1)+tail1(l))
  assert (c-hh).yes() and (c-pp*(1+2*pp*ex(-a*l)/l)).yes()
  print('early power envelope',mode,on,c,flush=True)
 # Pointwise transport improves strictly on the tail against CH and the unclipped spectral branch.
 assert (I('0.000000000001047198')-mix(Q(170),M1)).yes()
 assert (I('0.000000000001047198')-sum(c*weight(Q(170),d,a)*(1+1/(170*(1-a-Q(2,A)))) for c,d,a in M1)).yes()
 # Pure-logarithmic profiles. Finite cells use decreasing absolute
 # majorants at the left (admit the post-58 value at the join).
 for mode in [0,1]:
  exps=[2,3,4,5,6,7,8,9]
  on=[16,17,18,20,22,24,28,32,40,55,65,100,160,175,200]
  acc={k:I(0) for k in exps}
  out={}
  for j in range(3200-1,159,-1):
   l,r=Q(j,10),Q(j+1,10)
   d=delta(l,mode)
   if l<=58<r:d=mx(d,mix(Q(58),CH))
   if l<=Q("29.9")<r:d=mx(d,delta(Q("29.9"),mode,True))
   hh=d+J(l,mode,0)+tail1(l)
   pp=d/l+J(l,mode,1)+tail1(l)/l
   assert (Q(1,2)-pp).yes()
   for k in exps:acc[k]=mx(acc[k],(pp*(1+2*pp) if k%2 else hh)*r**k)
   if l.denominator==1 and l in on:out[int(l)]=acc.copy()
  a=[Q(1,8),Q(5,32)][mode];l=Q(320)
  h,p,_=pconst(l,mode)
  for b,l,k,cw,cp in LOGS:
   if mode!=b:continue
   res=out[l]
   for j,c in [(k,cw),(k+1,cp)]:
    tail=(p if j%2 else h)*ex(-a*320)*320**(j-1 if j%2 else j)
    w=mx(tail,res[j])
    assert (Q(c)-w).yes(),(mode,l,j,c,w)
   print('certified pure-log row',b,l,k,cw,cp,flush=True)
if __name__=='__main__':run()
