#!/usr/bin/python3.10
"""Endpoints and analytic/finite joins. No floating-point decision."""
import early, d02
from d02 import *
def certify_early(a,t,cs):
 z=early.run(a,t,cs)
 print("early cell join",a,t,cs,z.fmt(),flush=True)
def rec(l,r,ds,k,b,depth=0):
 for p in (200,201,300,301):
  if l<p<r:return mini(rec(l,F(p),ds,k,b,depth+1), rec(F(p),r,ds,k,b,depth+1))
 z=sl(l,r,ds,k)-err(l,r,b,k)
 if z.above(0):return z
 if depth==23 or not (sl(l,l,ds,k)-err(l,l,b,k)).above(0) or not (sl(r,r,ds,k)-err(r,r,b,k)).above(0):
  raise ValueError((str(l),str(r),b,k,z.fmt()))
 m=(l+r)/2
 return mini(rec(l,m,ds,k,b,depth+1),rec(m,r,ds,k,b,depth+1))
def ray(a,A,cs,k,b):
 a,A=F(a),F(A)
 if a<150:certify_early(a,150,cs);a=F(150)
 if a<A:
  v=rec(a,A,resid(cs),k,b)
  print('advanced cells',str(b),a,A,cs,v.fmt(),flush=True)
 assert tail(A,cs,k,b).above(0)
if 'early' in sys.argv:
 for a,c in [('36.53',0),('36.55','.01'),('36.6','.035'),('36.7','.08'),('36.76','.10'),
             ('36.962','.20'),('37.006','.219'),('39.542','.25'),('39.67','.30'),('39.90','.385'),
             ('39.998','.415'),('40.23','.50'),('41.36','.80'),('42.5','1')]:
  certify_early(a,'43.16',c)
 for a,z,c in [('44.7','65','1.18'),('45.1','65','1.22'),('46','63','1.25'),
               ('47.1','59','1.28'),('48.01','53','1.30')]:
  certify_early(a,z,c)
if 'rays' in sys.argv:
 for b,a,A,cs,k in [(B0,'47.68',199,[1,14],2),(B2,'47.68',185,[1,14],2),
                  (B0,'49',199,[1,14,2],2),
                  (B2,'49',185,[1,14,64],2),(B2,'49.4',185,[1,14,75],2),
                  (B2,'49.5',185,[1,14,76],2),
                  (B2,'168',185,[1,14,77],2),
                  (B2,'180',190,[1,14,131],2),(B2,'186',190,[1,14,142],3),
                  (B2,'188',188,[1,14,145],3),(B0,'222',223,[1,14,145],3),
                  (B2,'200',213,[1,14,145,1170],3),
                  (B2,'212.3',213,[1,14,145,1412],4),
                  (B2,'238',238,[1,14,145,1412,13985],5),
                  (B2,'260',264,[1,14,145,1412,13985,139000],5),
                  (B2,'213',214,[1,14,145,1412,2000],4),
                  (B0,'240',255,[1,14,145,1200],3)]:
  try:ray(a,A,cs,k,b)
  except (ValueError,AssertionError) as e: print("FAILED candidate ray",b,a,A,cs,e,flush=True)
if 'orders' in sys.argv:
 for j,x0,x2 in [(2,223,189),(3,256,213),(4,290,238),(5,324,264),(6,360,291),
                 (7,396,317),(8,431,344),(9,467,371),(10,503,398),(11,540,424),
                 (12,575,451),(15,685,533),(18,794,615),(19,830,642),(20,867,670),
                 (24,1013,779),(28,1160,889),(32,1307,999),(37,1490,1136),(43,1712,1303)]:
  cs=[coeff(i) for i in range(j+1)]
  for b,a in ((B0,x0),(B2,x2)):assert tail(a,cs,j+1,b).above(0)
# single branch normalized by exp(alpha*t), monotone in t once anchor is fixed.
def scaled(a,t,b):
 c,k=anc(a,b)
 return c*(1+I(1)/(b-F(2,a))/t)+k*I(t)/a*exp0(a-b*t)
for a,t,b,c in [(165,170,B2,'.33'),(550,600,B2,'.178'),(550,600,B0,'.013')]:
 assert scaled(a,t,b).below(c),(a,t,b,c,scaled(a,t,b).fmt())
assert (I('.33')*exp0(-F(170*5,32))).below('1.05e-12')
assert (I('.33')*exp0(-F(170,32))).below('.005')
assert (I('.178')*(I(601)/600*exp0(F(5,32))+I('2.02')+I('.178')*exp0(-F(600*5,32)))).below('.57')
assert (I('.013')*(I(601)/600*exp0(F(1,8))+I('2.02')+I('.013')*exp0(-F(600,8)))).below('.042')
for c,b,fac in [(28,B2,'.96'),(37,B0,'1')]:
 assert (I(c)*exp0(1-c*(1-b))).below(fac)
assert (I('.57')*I('.96')**40).below('.112')
assert (I(3)/13+I(4)*41/(40*27)+I('.001')).below('.384')
assert (I(2)/3-I(4)/40).above('.566')
assert F(3*81**41,2**520)<F(1,8)
assert (I('.0105')*(1-exp0(-F(3,4)))).above('.005')
assert (I(37)*exp0(1-F(37*5,32))).below(F(1,3))
assert (I('.57')*I(F(1,3))**40).below('.002')
assert (BH(200,B2)+residual(200,B2)).below('.28')
assert (I(F('27.1'))*exp0(1-F('27.1')*(1-B2))).above(1)
for L,a,c0,c2 in [(180,170,'.0669','.960'),(190,180,'.0634','.910'),
                  (200,190,'.0606','.8782'),(220,200,'.0582','.830'),
                  (250,220,'.0545','.776'),(300,250,'.0507','.721'),
                  (550,400,'.0425','.604'),(600,550,'.0397','.563')]:
 for b,c in [(B0,c0),(B2,c2)]:
  V=scaled(a,L-1,b)
  C=V*(I(L)/(L-1)*exp0(1-b)+I('2.02')+V*exp0(-(1-b)*L))
  assert C.below(c),(L,a,b,c,C.fmt())
 print('Li absolute gap budget',L,c0,c2)
assert ((I('.8782')/I('.0606'))*exp0(-F(200,32))).below('.028')
assert ((I('.2582')/I('.01831'))*exp0(-F(200,32))).below('.028')
assert (F(3,5)*exp0(F(1,2))).below(1)
print('strict Li-envelope comparison and linear all-order constants verified')
