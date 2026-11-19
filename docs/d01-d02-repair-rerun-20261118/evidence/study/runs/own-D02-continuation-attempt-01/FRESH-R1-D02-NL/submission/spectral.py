"""Paired B0/D02 exact dyadic certificates. Fractions are exact."""
from functools import lru_cache
from dyad import I,F,S,exp,ln,f,PI
H=3000175332800
h=ln(H)
b0=F(7,8); b2=F(27,32)
fore=F('.70')
start=100
cutoffs=((F(1,3),0),(F(2,5),0),(F(9,20),0),(F(1,2),2))
rs=[('.70','.75','6.1727','4.4992'),('.75','.80','7.7979','4.1006'),
    ('.80','.81','8.1610','3.6926'),('.81','.82','8.5373','3.6126'),
    ('.82','.83','8.9269','3.5326'),('.83','.84','9.3298','3.4526'),
    ('.84','.85','9.7461','3.3725'),('.85','.86','10.1759','3.2924'),
    ('.86','.87','10.6191','3.2123'),('.87','.88','11.0755','3.1321')]
rs=[tuple(map(F,row)) for row in rs]
p1=F('1.000000147');p2=F('1.78')
def aq(s):
 return (8*s-5)/3,5-2*s

def taylor(s,c,d,y):
 al,q=aq(s);w=I(1);z=1/I(al)
 for j in range(1,5):
  w=w*(q-j+1)/(al*y);z+=w/al
 return 2*c*exp(q*ln(y)-al*y)*z+2*d*exp(-y)*(y*y+2*y+2)

def choose(xs):
 xs=list(xs)
 return I(min(x.a for x in xs),min(x.b for x in xs),True)

def ceil(x,N):
 return F(-(-x.b*N//S),N)
def floor(x,N):
 return F(x.a*N//S,N)

def parts(b,step):
 for l,u,c,d in rs:
  if l>=b:break
  r=min(b,u)
  # fixed grid, truncated part (the cut-pair shares the same grid)
  n=-(-(u-l)//step)
  for j in range(n):
   a=l+j*(u-l)/n;z=min(r,l+(j+1)*(u-l)/n)
   if a>=r:break
   yield a,z,c,d

# Use exactly the same continuous piecewise-linear cap for both boundaries.
# Slope pieces together with constant clips; the clip is continuous.
@lru_cache(None)
def cap(b):
 ps=[];cur=None
 for l,u,c,d in parts(b0,F('.002')):
  C=ceil(taylor(l,c,d,h),10**10);D=ceil(taylor(u,c,d,h),10**10)
  assert C>D and (cur is None or cur<=C),(l,cur,C)
  if cur is None:cur=C
  m=(C-D)/(u-l)
  if cur>D:
   a=u-(cur-D)/m
   if a<b:ps.append((a,min(u,b),m))
   if b<=u:
    return min(cur,C-m*(b-l)),ps
   cur=D
  elif b<=u:return cur,ps
 raise ValueError(b)

@lru_cache(None)
def zw(v,b):
 # v is rational point only
 K,ps=cap(b);t=I(v)
 return K+sum(m*exp((u-b)*t)*(1-exp((l-u)*t))/t for l,u,m in ps)

def pscaled(t,b):
 return p1*exp((F(1,2)-b)*t)+p2*exp((F(1,3)-b)*t)

def terms(v,b,k,j):
 # Returns decay rates and positive pointwise majorants of the *relative*
 # psi residual divided by exp(-(1-b)*v).
 t=I(v);y=k*t-j
 C={ (F(1,3),0):F('.018'),(F(2,5),0):F('.026'),
      (F(9,20),0):F('.033'),(F(1,2),2):F('.040')}[k,j]
 # The ordinate quadratic can be bounded by .16*k² v², since
 # z<=kv+1 and the lower-order polynomial is -0.26*k*v+0.98.
 assert C>=F('.16')*k*k
 yield b-F(1,2)-F(2,v), C*t*t*exp((F(1,2)-b)*t), F(1,2)
 yield b-fore-F(2,v), C/2*t*t*exp((fore-b)*t), fore
 yield b+k-1-F(1,v), I('2.091')*t*exp((1-b-k)*t+j), 1-k-F(1,start)
 for l,u,c,d in parts(b,F('.010')):
  al,q=aq(l);Y=k*v-j
  # tangent bound; the scaled term has negative log derivative at
  # least the listed positive rate on [v,infty).
  den=al-q/Y
  assert den>0
  rate=b-u+k*(al-q/Y)
  Y0=k*start-j
  lam=u-k*al-F(2,start)-q*k/(Y0*Y0*(al-q/Y0))
  yield rate, (2*c/den)*exp((u-b)*t+q*ln(y)-al*y),lam
  yield b-u+k*(1-F(2,Y)), 2*d*(y*y+2*y+2)*exp((u-b)*t-y),u-k-F(2,start)

def pieces(v,b,k,j):
 return ((r,y) for r,y,_ in terms(v,b,k,j))

@lru_cache(None)
def profile(v,b):
 t=I(v);delta=1-b
 z=zw(v,b)
 Es=[];Ms=[];M1=[];Rs=[]
 for k,j in cutoffs:
  ts=list(terms(v,b,k,j));ps=[(r,y) for r,y,g in ts]
  assert all(r>0 and g>0 for r,y,g in ts)
  Es.append(sum(y for r,y in ps))
  Ms.append(sum(y*(1+1/(delta+r)) for r,y in ps))
  M1.append(sum(y*(1+(1+1/t)/(delta+r)) for r,y in ps))
  Rs.append(sum(y*(1+1/(t*g)) for _,y,g in ts))
 B=I('1.000100294')*exp((F(1,2)-b)*t)+I('2.67')*exp((F(1,3)-b)*t)
 # product / reciprocal sum use positive signed higher-power correction;
 # these return common conservative absolute coefficients.
 m2=z+choose(Ms)+B
 m1=z+choose(M1)+B
 # spectral component and theta plus history for pi:
 rp=(1+2/(H*t))*z+choose(Rs)+(1+4/t)*pscaled(t,b)+I('3e-16')*t*exp(100-b*t)
 return z,choose(Es),m2,m1,rp

@lru_cache(None)
def metc(v,b):
 t=I(v)
 _,_,m2,m1,_=profile(v,b)
 Y=m1*exp(-(1-b)*t)/t
 assert Y.below(1)
 return m2,m1/(1-Y)

def basic():
 from mcert import basics
 basics()
 for k,j in cutoffs:
  t=I(start); y=k*t-j
  assert (exp(y)-100).above(0)
  assert ((exp(t/2)-2)/5-exp(y)).above(0)
  assert (y-h).above(0)
  for b in (b0,b2):
   assert all(dec>0 and grow>0 for dec,_,grow in terms(start,b,k,j))
   for l,u,c,d in parts(b,F('.010')):
    al,q=aq(l);Y=k*start-j
    val=u-k*al-F(2,start)-q*k/(Y*Y*(al-q/Y))
    assert val>F(1,4)
  assert F(2,100)<k and F('.98')<F('.26')*k*100
 for b in (b0,b2):
  print('b, exact limiting coefficient:',b,cap(b)[0],flush=True)
 for v in [100,110,120,130,140,150,155,160,165,170,175,180,185,190,200,250,300,500,1000,5000,20000]:
  row=[]
  for b in (b0,b2):
   p,q=metc(v,b)
   c=ceil(I(max(p.a,q.a),max(p.b,q.b),True),10**6)
   assert p.below(c) and q.below(c)
   row.extend([str(c),str(ceil(profile(v,b)[-1],10**6))])
  print('M/pi paired: v, c0, r0, c2, r2',v,*row,flush=True)
if __name__=='__main__':basic()
