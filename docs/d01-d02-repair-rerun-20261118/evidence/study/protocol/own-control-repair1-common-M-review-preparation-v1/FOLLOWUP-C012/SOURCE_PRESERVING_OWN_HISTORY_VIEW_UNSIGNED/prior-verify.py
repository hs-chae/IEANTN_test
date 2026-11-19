from model import *
import json
def li_anchor(L):
 # gamma interval: H_2048-log(2048)-1/(4096), error < 1/(2048)^2.
 n=2048
 harmonic=sum((I(1)/j for j in range(1,n+1)),I(0))
 g=harmonic-ln(n)-1*I(Q(1,2*n))+I(0,Q(1,n*n))
 t=I(1);s=I(0)
 for k in range(1,180):t=t*L/k;s+=t/k
 return g+ln(L)+s+I(0,Q((t/4).b,S))
def basic():
 # pi > 25/8 follows e.g. from the perimeter of the inscribed 24-gon;
 # farther comparisons requiring only pi < 22/7 are not used.
 def atan(t,n):
  return sum((-1)**j*t**(2*j+1)/(2*j+1) for j in range(n))
 assert 32*(4*atan(Q(1,5),16)-atan(Q(1,239),17))>PI8
 assert 4*(4*atan(Q(1,5),17)-atan(Q(1,239),16))<Q("3.141594")
 z=li_anchor(Q(30))/ex(30)-f(Q(30))
 assert z.yes() and (Q(2*factorial(N),30**(N+1))-z).yes()
 z24=li_anchor(Q(24))/ex(24)-f(Q(24))
 assert z24.yes() and (Q(3*factorial(N),24**(N+1))-z24).yes()
 assert (ln(10)*13-Q("29.9")).yes()
 assert (ln(10)*4-16).b<0
 assert (ln(10)*19-Q('43.74')).yes()
 assert (ln(Q('2.169')*10**25)-58).yes()
 assert (shifted(Q(200),M1,Q(5,32))-1).b<0
 assert all(d<=200*(a-Q(5,32)) for c,d,a in M1)
basic()
ROWS=[
 # mode,k,onset,coefficient; profile adds this coefficient to the first k terms
 (0,0,'36.984','0.001'),(0,0,'37','0.009'),(0,0,'38','0.41'),(0,0,'40','0.92'),(0,0,'42','1'),
 (0,1,'43','4'),(0,1,'46','10'),(0,1,'55','14'),
 (0,2,'60','19'),(1,2,'60','81'),(1,2,'176','120'),(0,2,'202','120'),
 (1,2,'190','145'),(0,2,'220','145'),
 (1,3,'190','600'),(0,3,'223','600'),(1,3,'200','1200'),(0,3,'237','1200'),
 (1,4,'228','13000'),(0,4,'281','13000'),
 (1,5,'252','130000'),(0,5,'310','130000'),
 (1,6,'275','1300000'),(0,6,'350','1300000'),
 (1,7,'310','10000000'),(0,7,'390','10000000'),
 ]
END=320
def check_tail():
 for b,k,t,c in ROWS:
  c=Q(c)
  if c==C[4+k]:k+=1;c=Q(0)
  q=max(Q(END),Q(t))
  v=C[4+k]+sum(Q(a)*q**(k+4-i) for i,a in enumerate(C) if i>4+k and a<0)-tail_err(q,b,k)
  assert (v-c).yes(),(b,k,t,c,v)
def run():
 check_tail()
 # positive polynomial part at cell right; negative part left;
 # error at left with increasing powers at right, all joins accounted for.
 for b in (0,1):
  rows=[(k,Q(t),Q(c)) for bb,k,t,c in ROWS if b==bb]
  lim=0
  ends=sorted({Q(a,20) for a in range(37*20,END*20+1)} | {t for k,t,c in rows if t<=END})
  for l,r in zip(ends,ends[1:]):
   for k in set(k for k,t,c in rows if t<=l):
    c=max(c for j,t,c in rows if j==k and t<=l)
    if not (lower(l,r,b,k)-c).yes():
     def sub(a,z,d):
      v=lower(a,z,b,k)
      if (v-c).yes():return
      assert d>0,(b,k,a,c,v)
      m=(a+z)/2
      sub(a,m,d-1);sub(m,z,d-1)
     sub(l,r,12)
   lim+=1
  print('Ramanujan mode',b,'primary cells',lim,flush=True)
def finiteE(u):
 return u*16/PI8*ex(8-u)+sum(I(c)*ex(-a*u)*(1+1/(u*(1-a-Q(1,8))))
     for c,a in [('1.751000147',Q(1,2)),('1.78',Q(2,3))])
def finite_lower(l,r):
 main=sum(Q(c)*(r if c>0 else l)**(4-i) for i,c in enumerate(C) if i>=4 and c)
 h=Q(3,2)*hrem(l)
 return main-r**4*(l/(l-1)*finiteE(l-1)+2*l*f(l)*h+h*h)
def finite_rows():
 for s,c in [('28','0.015'),('29','0.53')]:
  l=Q(s);r=Q('29.9')
  for j in range(int(l*200),int(r*200)):
   lo,hi=Q(j,200),Q(j+1,200)
   assert (finite_lower(lo,hi)-Q(c)).yes(),(s,c,lo,finite_lower(lo,hi))
  print('Finite quantitative island',s,'29.9',c)
if __name__=='__main__':finite_rows();run()
