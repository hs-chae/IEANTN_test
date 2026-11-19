from fractions import Fraction as F
from math import factorial as fac,comb
from functools import lru_cache
S=10**72
@lru_cache(maxsize=20000)
def ex(x):
 x=F(x); assert x>=0
 k=0
 while x>1: x/=2;k+=1
 t=s=F(1)
 for i in range(1,39):
  t*=-x/i;s+=t
  if i==37: lo=(s*S).__floor__()
 hi=(s*S).__ceil__()
 for _ in range(k):lo=lo*lo//S;hi=(hi*hi+S-1)//S
 return F(lo,S),F(hi,S)
def E(x):return ex(x)[1]
def EP(x):return 1/ex(x)[0]
H=3*10**12
assert EP(F('28.72'))<H<1/E(F('28.74')) and EP(F('3.35'))<F('28.72')
assert EP(58)<2169*10**22 and EP(F('39.47'))<139*10**15
assert EP(29)<10**13 and EP(18)<66000000
assert F(1,225)+F('1.8642')/200**2+F('2.091')/200*E(F(200,24))<F('.0045')
assert F('.65')/E(17)>10**7 and F('.65')*EP(29)<H
assert F('2.26')<F('2.27') and EP(F('2.26'))<F('6.283')/F('.65')<F('6.284')/F('.65')<1/E(F('2.27'))
assert 20**2*EP(10)/25+20*EP(10)/25<400000
assert F('1.000001')+F('1.78')*E(F(34,6))<F('1.02')
D=[]
for row in '''.80 8.162 3.693 6.6 .81
.81 8.538 3.613 2.74 .82
.82 8.928 3.533 1.16 .83
.83 9.331 3.453 .50 .84
.84 9.747 3.373 .215 .85
.85 10.177 3.293 .091 .86
.86 10.621 3.213 .039 .87
.87 11.077 3.133 .018 .873
.873 11.077 3.133 .014 .875'''.splitlines():
 s,c1,c2,b,sb=map(F,row.split());d=1-8*(1-s)/3;r=5-2*s
 bd=2*(c1*E(d*F('28.72'))*F('28.74')**4*E((4-r)*F('3.35'))/(d-r/F('28.72'))+c2/H*F('28.74')**2/(1-2/F('28.72')))
 assert bd<b,(s,float(bd),float(b))
 D.append((b,0,1-sb))
P=[(F('1.000001'),0,F(1,2)),(F('1.78'),0,F(2,3))]
DEN=[(F('.018'),2,F(1,5)),(F('2.091'),1,F(1,3))]+D
# Uniform layer cake: 2 sum_{beta >= s, gamma>H} 1/gamma
# <= .01058 exp(91.2*(.875-s)), for .8 <= s <= .875.
j0=F('28.7296');j1=F('28.7297'); d0=1-F(8,15); r0=F('3.4')
assert EP(j0)<H<1/E(j1) and EP(F('3.3579'))<j0
assert (F(8,3)*j1+2*F('3.36')+(F(8,3)+2/j0)/(d0-r0/j0))<F('91.2')
assert EP(F('3.36'))>j1
bc=2*(F('11.077')*E(F(2,3)*j0)*j1**4*E(F('.75')*F('3.3579'))/(F(2,3)-F('3.25')/j0)+F('3.693')/H*j1*j1/(1-2/j0))
assert bc<F('.01058')
def layer(L):
 return F('.01058')*L/(L-F('91.2'))*E(L/8)
def gl(L):
 return g(L,DEN[:2])+layer(L)
a=F('1.048e-12')
CH=[(a,0,F(0)),(F('113.67'),0,F(1,2))]
CO=[(F('.005'),2,F(1,8))]
NEW=[(F(1,64),2,F(1,8))]
def g(L,Q):return sum(b*L**m*E(c*L) for b,m,c in Q)
def tr(L,J,Q):return sum(b*L**m*E(c*L)*(1+1/((1-c-F(2-m,J))*L)) for b,m,c in Q)
@lru_cache(maxsize=20000)
def qc(L):return tr(L,20,CH+P)+400000*L*E(L)
@lru_cache(maxsize=20000)
def qa(L,J,den):
 Q=(DEN if den else CO)+P
 return tr(L,J,Q)+(qc(F(J))+g(F(J),CH+P))*L/J*E(L-J)
@lru_cache(maxsize=20000)
def ql(L):
 J=150
 anch=(qc(F(J))+g(F(J),CH+P))*L/J*E(L-J)
 d=1-F(1,8)-F(2,J)-F('91.2')/(J*(J-F('91.2')))
 return tr(L,J,DEN[:2]+P)+layer(L)*(1+1/(d*L))+anch
M1=F('91.2');M2=F('88.9');Dlt=F('.02')
ds=1-F(8,3)*(1-F('.855'));rs=5-2*F('.855')
assert F(8,3)*j1+2*F('3.36')+(F(8,3)+2/j0)/(ds-rs/j0)<M2
@lru_cache(maxsize=20000)
def qlt(L):
 J=150
 anch=(qc(F(J))+g(F(J),CH+P))*L/J*E(L-J)
 d1=1-F(1,8)-F(2,J)-M2/(J*(J-M2))
 d2=1-F(1,8)-Dlt-F(1,J)-1/(J-M1)-1/(J-M2)
 t1=F('.01058')*L/(L-M2)*E(L/8)
 t2=F('.01058')*(M1-M2)*L/((L-M1)*(L-M2))*E(L/8+Dlt*(L-M2))
 return tr(L,J,DEN[:2]+P)+t1*(1+1/(d1*L))+t2*(1+1/(d2*L))+anch
def local(l,h,den,upper=False):
 z=[]
 if h<=58:z.append(l**3*E(l/2)/25)
 if l>=20:z.append(qc(l))
 if l>=34 and h<=58:z.append((F('.0398')*l*l-F('.305')*l+F('6.82'))*E(l/2)+400000*l*E(l))
 if l>=150 and den:z += [qa(l,150,True),ql(l),qlt(l)]
 if l>=200:z.append(qa(l,200,False))
 if upper and h<=F("39.47"):z.append(F(0))
 return min(z)
N=20;A=[fac(j) for j in range(N+1)]
B=[sum(comb(j,k)*fac(k) for k in range(j+1)) for j in range(N+1)]
C=[sum(A[k]*A[j-k] for k in range(max(0,j-N),min(j,N)+1)) for j in range(2*N+1)]
Z=[B[j]-C[j] for j in range(N+1)]
assert Z[:5]==[0,0,0,0,1] and min(Z[4:])>=1
Z=Z[4:]
V=24
ss=sum(F(V**i,i*fac(i)) for i in range(1,200))
pv=sum(F(c,V**(j+1)) for j,c in enumerate(A))
assert ss+F(1,10)-pv/E(V)<3 and ss-pv*EP(V)>-3
assert F(V**200,200*fac(200))*2<F(1,10)
def sm(L):return sum(c/L**j for j,c in enumerate(A))
def r(L):return 12*fac(N+1)/L**(N+1)+10*L*E(L)
@lru_cache(maxsize=20000)
def pen(l,h,den,forced=False):
 qq=lambda L,H,u=False: qa(L,150 if den else 200,den) if forced else local(L,H,den,u)
 t=r(l)+qq(l,h,True)
 return sum(C[j]/l**(j-4) for j in range(N+1,2*N+1))+h**4*(2*sm(l)*t+t*t+10*l*E(l-1)+l/(l-1)*qq(l-1,h-1))
def win(l,h,p,den):
 z=[c-(p[i] if i<len(p) else 0) for i,c in enumerate(Z)]
 return sum(d/(h if d>=0 else l)**i for i,d in enumerate(z))>pen(l,h,den)
def windows(l,h,p,den,d=F(1,4)):
 l,h=F(l),F(h)
 while l<h:
  if l<F('39.47'):u=min(l+F(1,100),F('39.47'),h)
  elif l<60:u=min(l+F(1,100),F(60),h)
  elif 185<=l<195:u=min(l+F(1,100),F(195),h)
  elif 835<=l<845:u=min(l+F(1,100),F(845),h)
  else:u=min(l+d,h)
  if not win(l,u,p,den):return l,u
  l=u
def tail(J,p,den):
 J=F(J);z=[c-(p[i] if i<len(p) else 0) for i,c in enumerate(Z)]
 assert min(z)>=0
 j=next(i for i,c in enumerate(z) if c>0)
 assert j<N-3 and j+5<=J-1
 assert all(j+4+m<=c*(J-1) for _,m,c in (DEN if den else CO)+P)
 assert z[j]>J**j*pen(J,J,den,True)
def run():
 cases=[
 ('36.85',400,['.03']),('37',400,['.09']),('37.15',400,['.10']),('39.5',400,['.12']),
 ('39.6',400,['.16']),('40',400,['.32']),('40.5',400,['.50']),
 ('41',400,['.65']),('42.2',400,['.90']),('42.85',400,[1]),
 ('45.4',400,[1,10]),('46.2',400,[1,12]),('46.8',400,[1,13]),
 ('47.4',400,[1,14]),('48',420,[1,14,3]),('48',420,[1,14,5]),('48',420,[1,14,6]),('49',420,[1,14,25]),('49',420,[1,14,30]),
 ('215',420,[1,14,140]),('217',420,[1,14,140]),('222',420,[1,14,145]),('225',420,[1,14,145]),
 ('270',420,[1,14,145,1412]),('420',520,Z[:8]),('510',600,Z[:10]),
 ('620',730,Z[:13]),('780',870,Z[:16]),('840',920,Z[:16]),('850',920,Z[:16]),('900',1000,Z[:16])
 ]
 for l,J,p in cases:
  p=list(map(F,p))
  fail=windows(l,J,p,True)
  if fail:print('FAIL',l,[str(v) for v in p],fail,flush=True);continue
  try:tail(J,p,True)
  except AssertionError:print('FAIL TAIL',l,[str(v) for v in p],flush=True);continue
  print('PASS',l,J,[str(v) for v in p],flush=True)
 for l,h,p in [('37.5','39.47',['.28']),('38.1','39.47',['.50']),
               ('39','39.47',['.74']),('55','119',[1,14,145]),
               ('52','135',[1,14,130]),('50','150',[1,14,100])]:
  p=list(map(F,p))
  fail=windows(l,h,p,True)
  print('FAIL BOUNDED' if fail else 'PASS BOUNDED',l,h,[str(v) for v in p],fail,flush=True)
if __name__=='__main__':run()
