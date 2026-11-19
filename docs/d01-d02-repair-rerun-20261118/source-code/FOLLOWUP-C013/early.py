#!/usr/bin/python3.10
from verify import *
from functools import lru_cache
# Additional heights entirely within the original verified RH range.
heights=[10**6*k for k in range(10,151,2)]+[200*10**6,300*10**6,500*10**6,800*10**6,10**9]
assert exp0(21).above(max(heights))
base=[]
for T in heights:
 u=log(I(T)/(2*piB))
 A=piB/(T-1)+I('3.3')/T**2
 C=(u*u-u/3)/(2*piB)
 assert C.above(2)
 K=v1(21)+I('1.4')*exp0(F(-21,2))+A+C*exp0(F(-21,2))+1050*exp0(-21)
 base.append((A,C,K))
@lru_cache(None)
def vj(t,side):
 c=Jcor(t) if side=='1.06' else -(1+I(2)/t+I(8)/t**2)
 assert 35<=t<=58 and exp0(F(35,2)).above(88789)
 return mini(*(A+(C+c)*exp0(-t/2)+K*t/21*exp0(21-t) for A,C,K in base))
def W(t,side):
 q=w(t,side)
 return mini(q,vj(t,side)) if 35<=t<58 else q
# Every cell starts in a branch valid all the way to its right endpoint.
cuts=(F('39.471'),F(58),F(59),F(75),F(76),F(200),F(201),F(300),F(301))
assert exp0(cuts[0]).below(139000000000000000)
def erl(l,r):
 z=I(r); d=z**5/(l-1)*W(l-1,'1.06')
 if r>cuts[0]:
  q=W(l,'-.97');d+=z**4*q*(I('2.08')+q)
 return d
def cell(l,r,c):
 return low_res(l,r,list(map(F,c)) if isinstance(c,(tuple,list)) else [F(c)],0)-erl(l,r)
def run(a,b,c,depth=0):
 a,b=F(a),F(b)
 for p in cuts:
  if a<p<b:return mini(run(a,p,c,depth+1),run(p,b,c,depth+1))
 w=cell(a,b,c)
 if w.above(0):return w
 if depth>=28 or not cell(a,a,c).above(0) or not cell(b,b,c).above(0):
  raise ValueError((str(a),str(b),str(c),w.fmt()))
 m=(a+b)/2
 return mini(run(a,m,c,depth+1),run(m,b,c,depth+1))
if __name__=='__main__':
 for t in ['36.52','36.53','36.54','36.55','36.58','36.60','36.65','36.7','36.8','36.95','36.96','36.97','37.0','39.471001','39.50','39.58','39.60','39.66','39.90','39.98','40.48','40.49','41.90','43.14']:
  t=F(t); print(t,(lowpoly(t,t)-erl(t,t)).fmt())
