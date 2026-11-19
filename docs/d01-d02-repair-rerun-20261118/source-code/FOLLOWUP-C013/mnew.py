#!/usr/bin/python3.10
"""Exact whole-ray Mertens checks; analytic monotonicity is in d02-proof.md."""
from d02 import *
Hs=[10**7*2**j for j in range(19)]+[3000175332800]
tc=[]
for T in Hs:
 u=log(I(T)/(2*piB))
 tc.append((T,piB/(T-1),(u*u-u/3)/(2*piB)))
def chcap(l,r):
 l,r=F(l),F(r); z=I(l)**2
 sqrt=z*exp0(-l/2)
 cubes=I('2.67')*z*exp0(-2*l/3)
 pp=I('1.001')*sqrt+cubes+3*z*exp0(-99*l)
 q=mini(*(A*r*r+C*sqrt+piB**2*r/(3*T*T) for T,A,C in tc if exp0(l).above(max(10**9,T))))
 v=q+pp
 return v/(1-v/I(l)**3)
def cap(t,b):
 return mcap(F(t),b,False) # upper cap covers weighted too
def logcap(t,b):
 return cap(t,b)*I(t)**2*exp0(-(1-b)*F(t))
def plusmax(*q):return I.raw(max(x.a for x in q),max(x.b for x in q))
def finite(a,z):
 a,z=F(a),F(z); h=F(1,4)
 knots=sorted({a,z}|{k*h for k in range(int(a/h)+1,int(z/h)+1) if a<k*h<z})
 return plusmax(*(chcap(l,r) for l,r in zip(knots,knots[1:])))

if 'explore' in sys.argv:
 for t in [150,155,160,165,168,169,170,175,180,190,191,192,193,195,200,220,230,240,250,300,360,400,550,800,1000,1400]:
  print(t,cap(t,B0).fmt(),cap(t,B2).fmt(),logcap(t,B0).fmt(),logcap(t,B2).fmt(),flush=True)
 for a in [26,30,35,40,45,50,58,65,100]:
  print('ray',a,[plusmax(finite(a,z),logcap(z,b)).fmt() for z,b in [(191,B0),(170,B2)]],flush=True)
else:
 for t,b,c in [(150,B2,'.348'),(160,B2,'.320'),(169,B2,'.300'),(170,B2,'.299'),
               (180,B2,'.282'),(190,B2,'.269'),(200,B2,'.2582'),(220,B2,'.242'),
               (210,B2,'.25'),(250,B2,'.225'),(300,B2,'.2071'),(332,B2,'.20'),
               (400,B2,'.189'),(550,B2,'.1761'),(800,B2,'.167'),(1250,B2,'.16'),
               (200,B0,'.01831'),(300,B0,'.01474'),(800,B0,'.01187')]:
  z=cap(t,b)
  assert z.below(c),(b,t,c,z.fmt())
  print('power',b,t,c,z.fmt(),flush=True)
 for a,z,b,c in [(26,190,B0,'.0503'),(30,190,B0,'.0093'),(35,190,B0,'.0013'),
                 (40,190,B0,'.000182'),(45,190,B0,'.000024'),(50,190,B0,'.00000301'),
                 (58,190,B0,'1.004e-7'),(65,190,B0,'3.781e-8'),(100,190,B0,'3.781e-8'),
                 (65,169,B2,'3e-8'),(100,169,B2,'3e-8')]:
  v=plusmax(finite(a,z),logcap(z,b))
  assert v.below(c),(a,z,b,c,v.fmt())
  print('log ray',a,z,b,c,v.fmt(),flush=True)
 for a,b,c in [(175,B2,'1.182e-8'),(177,B2,'1e-8'),(192,B2,'1e-9'),(200,B2,'2.77e-10'),
               (200,B0,'1.017e-8'),(201,B0,'1e-8'),(220,B0,'1e-9'),(230,B0,'3e-10')]:
  v=logcap(a,b)
  assert v.below(c),(a,b,c,v.fmt())
  print('small log ray',a,b,c,v.fmt(),flush=True)
 assert (I('.300')*exp0(-F(169,32))).below('.004')
 assert (I('.300')*exp0(-F(845,32))).below('1.03e-12')
 assert (I('.300')*169**2*exp0(-F(845,32))).below('3e-8')
 print('model dominance from 169 verified')
