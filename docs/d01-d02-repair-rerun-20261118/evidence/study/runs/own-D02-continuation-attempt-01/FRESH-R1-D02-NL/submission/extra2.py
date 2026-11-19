"""Fine-cap coefficient/onset improvements, replay independently from m2.py."""
import spectral,m2
from refine2 import new_Z,fine_cap
from spectral import F,I,exp,metc,b0,b2
spectral.zw=m2.zw=new_Z
if __name__=='__main__':
 for b,c,V in [(b0,'.018865','188.909'),(b2,'.29389','168.7')]:
  print('fine cap',b,fine_cap(b)[0],flush=True)
  m2.testexp(F(V),b,c)
 m2.roots('.29389',m2.small('.29389'))
 for c in ('.290','.25','.20','.175','.15','.147','.1465'):
  lo=100;hi=100000
  def ok(v):return all(z.below(c) for z in metc(v,b2))
  assert ok(hi)
  while lo<hi:
   m=(lo+hi)//2
   if ok(m):hi=m
   else:lo=m+1
  assert ok(lo)
  print('fine cap, speed target, onset',c,lo,flush=True)
 # For the entire fixed L>=200 comparison/savings, use monotone e^{-L/32}.
 a0=200
 p,q=metc(a0,b2);fac=exp(-I(a0)/32)
 assert (p*fac).below('.00049') and (q*fac).below('.00049')
 assert F('.00049')<fine_cap(b0)[0]/20
