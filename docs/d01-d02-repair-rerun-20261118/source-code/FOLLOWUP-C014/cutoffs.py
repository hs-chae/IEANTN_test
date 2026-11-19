"""Exact signs in the unit intervals immediately before the original cutoffs."""
from edge import lograt
from certify import F, ex, E, EP
from pathlib import Path
import sys

def rounded(a,b):
 S=10**35
 return F((a*S).__floor__(),S),F((b*S).__ceil__(),S)
def logball(a,b):
 return rounded(lograt(a)[0],lograt(b)[1])
def verify(src):
 S=2**61
 ar={}
 for v in Path(src).read_text().replace(r'\n','\n').splitlines():
  if v.startswith('probe '):
   x,*a=map(int,v.split()[1:])
   ar[x]=[(F(a[i],S),F(a[i+1],S)) for i in range(0,len(a),2)]
 # No prime at last point: 2278382, 912560 even; 2278383 divisible by 3.
 for n,kind,elo,ehi,p,c in [
  (912559,3,'.9972','.9975',2,F('.3')),
  (2278382,0,'.11','.12',3,F('.2')),
  (2278381,1,'.57','.59',3,F('.2')),
  (2278381,2,'.70','.72',3,F('.2'))]:
  La,Lb=logball(F(n),F(n))
  ra,rb=logball(La,Lb)
  def bound(y):
   x=F(n)+y
   l,h=logball(x,x);cl,ch=logball(l,h)
   al,ah=ar[n][1 if kind==0 else 3 if kind==3 else 2]
   if kind==3:
    a,b=al+La-h,ah+Lb-l
    assert 0<a<b<l/2
   else:
    a,b=al+ra-ch,ah+rb-cl
    assert 0<a<b<F(1,10)
    if kind==1:a,b=1-E(a),1-ex(b)[0]
    if kind==2:a,b=1/E(a)-1,EP(b)-1
   return a*l**p,b*h**p
  a,b=F(elo),F(ehi)
  assert 0<a<b<1
  assert bound(F(0))[0]>c and bound(F(1))[1]<c
  assert bound(a)[0]>c and bound(b)[1]<c,(kind,float(bound(a)[0]),float(bound(b)[1]))
  print('cutoff',kind,n,elo,ehi)
if __name__=='__main__':verify(sys.argv[1] if len(sys.argv)>1 else 'finite_final.txt')

