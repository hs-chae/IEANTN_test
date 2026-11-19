"""B0-only quantitative bounded window at much earlier log x."""
from cert import I,F,exp,ln,PI,f
from higher2 import poly,anchor
from math import isqrt
from functools import lru_cache

@lru_cache(None)
def history():
 N=10000;t=ln(N)
 ps=[q for q in range(2,N+1) if all(q%p for p in range(2,isqrt(q)+1))]
 theta=sum((ln(q) for q in ps),I(0))
 y=ln(t)+I(-1,1);w=I(1)
 # The first 100 terms leave less than 2*10^101/101! for t<10.
 assert t.below(10)
 for j in range(1,101):
  w=w*t/j;y+=w/j
 y+=I(0,F(2*10**101,f(101)))
 C=len(ps)-y-(theta-N)/t
 assert C.above(F('-6.28')) and C.below(20)
 assert (I(F(1,2))-2/t).above('.28')
 assert (I('1.751000147')+I('1.78')*exp(-t/6)).below('2.14')
 r=I('19.3')
 assert (I('1.751000147')+I('1.78')*exp(-r/6)).below('1.83')
 print('mid anchor at',N,'pi',len(ps),'C_N',str(C),flush=True)
 return I('6.28')+(I('2.14')/I('.28'))*exp(r/2)/r**2

def signloss(l,u):
 t=I(l);v=t-1
 return I(u)**4*t/v*(I('1.83')*exp(-v/2)*(1+1/(v*(I(F(1,2))-2/I('19.3'))))+history()*v*exp(-v))
def main(lo,hi,c):
 n=10;p=poly(n)
 assert F(lo)>=2*n+6
 assert exp(I(F(hi)-1)).below(10**13)
 assert exp(I(hi)).below(139*10**15)
 def bound(l,u):
  z=I(1/u,1/l)
  val=I(0)
  for q in p[:3:-1]:val=q+z*val
  return val-signloss(l,u)
 def cell(l,u):
  if (bound(l,u)-I(c)).above(0):return 1
  assert u-l>F(1,100000),(l,u,c,str(bound(l,u)))
  m=(l+u)/2
  return cell(l,m)+cell(m,u)
 t=F(lo);H=F(hi);k=0
 while t<H:
  v=min(H,t+F(1,25))
  k+=cell(t,v);t=v
 print('mid closed',lo,hi,c,k,flush=True)
if __name__=='__main__':
 anchor(10)
 from sys import argv
 if len(argv)>1:
  for v in map(F,argv[1:]):print(v,str(sum(c/I(v)**(i-4) for i,c in enumerate(poly(10)) if i>=4)-signloss(v,v)),flush=True)
 else:
  for x,c in [('28','.01'),('28.2','.12'),('28.5','.28'),('29','.50'),('29.5','.69'),('30','.85'),('30.6','1'),('30.9','1.06')]:
   main(x,'30.93',c)
