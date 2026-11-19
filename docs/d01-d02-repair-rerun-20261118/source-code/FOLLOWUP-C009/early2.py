"""Input-independent refinement of signed finite prime-count history."""
from cert import I,F,S,PI,a,exp,ln,gl,U,err,qr
from functools import lru_cache
from bisect import bisect_left
from math import ceil

V=F('29.9');A=F('33.3');W=F('58')
E=exp(1)
H=3000175332800
mult=list(map(F,['1','1.1','1.17','1.25']))
def test():
 assert exp(I(10)).above(10000) and exp(I(V)).below(10**13)
 assert (2000+exp(5)/(4*PI)).below(2020)
 assert (I('1.751000147')+I('1.78')*exp(-I(F(10,6)))).below('2.1')
 for m in mult:
  assert (m*2*PI**2*exp(I(A)/2)/I(A)).above(10**7)
  assert (m*2*PI**2*exp(I(W)/2)/I(W)).below(H)
  assert (exp(I(A)/2)*I(A)/(m*2*PI**2)).above(1)
 assert exp(I(A)).above(10**9)

def smallest(xs):
 return min(xs,key=lambda v:v.b)
@lru_cache(None)
def ca(l,u,positive):
 # Enclose an upper bound for the coefficients on the entire cell:
 # theta relative signed magnitude <= ca * exp(-t/2).
 t=I(l,u)
 base=t*t/(8*PI)
 cand=[base,I(115)+a*exp(t/2)]
 if l>=A:
  for m in mult:
   T=m*2*PI**2*exp(t/2)/t
   z=ln(T/(2*PI))
   # T0 center is >=1. For negative side omit it, positive bound it.
   errC=(z*z-z/3)/(2*PI)+(t/(2*m*PI))/(1-1/T)
   if positive:errC=errC+PI**2*exp(t/2)/(3*T**2)-I('.9999')
   else:errC=errC+I('1.000000147')+I('1.78')*exp(-t/6)
   cand.append(errC)
 return smallest(cand)

@lru_cache(None)
def history(positive):
 H0=I(2020)
 if not positive:H0+=7*exp(I(V)/2)/I(V)**2
 endpoints=[V];vals=[H0]
 for L,R in [(V,A),(A,W)]:
  l=L
  while l<R:
   u=min(l+F(1,50),R)
   H0+=ca(l,u,positive)*exp(I(u)/2)/I(l)**2*(u-l)
   endpoints.append(u);vals.append(H0)
   l=u
 return endpoints,vals

@lru_cache(None)
def improved(l,u,pos=False):
 assert l>=V and u<=W
 endpoints,vals=history(pos)
 h=vals[bisect_left(endpoints,u)]
 # exp(-v/2) and v exp(-v) are decreasing: upper at l.
 return ca(l,u,pos)*exp(-I(l)/2)+h*l*exp(-I(l))

def bound(l,u,side):
 y=smallest([err(I(l-1),u-1),improved(l-1,u-1)] if u-1<=W else [err(I(l-1),u-1)])
 if side:z=I(0)
 else:z=smallest([err(I(l),u,True),improved(l,u,True)] if u<=W else [err(I(l),u,True)])
 return I(u)**4*(I(l)/(I(l)-1)*y+(2*U(I(l))+z)*z)
def check(lo,hi,c,side=False,var=0,step='.01',verbose=True):
 l=F(lo);hi=F(hi);step=F(step);k=0
 if side:assert exp(I(hi)).below(139*10**15)
 def cell(l,u):
  d=gl(l,u)-bound(l,u,side)-I(c)-(14/I(l) if var else 0)-(I(var)/I(l)**2 if var else 0)
  if d.above(0):return 1
  assert u-l>F(1,100000),(l,u,c,var,str(d))
  m=(l+u)/2
  return cell(l,m)+cell(m,u)
 while l<hi:
  u=min(l+step,hi);k+=cell(l,u);l=u
 if verbose:print('early closed',lo,hi,c,side,var,k,flush=True)

if __name__=='__main__':
 test()
 from sys import argv
 if len(argv)>1:
  for v in map(F,argv[1:]):
   print(v,gl(v,v)-bound(v,v,v<=F('39.47')))
