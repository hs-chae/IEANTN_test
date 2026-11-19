from higher2 import anchor,poly,active
from spectral import F,b0,b2
def bound(b,n,k,j,c):
 lo=100*max(151,8*j+1,2*n+6);hi=10**6
 assert active(F(hi,100),n,k,j,c,b)
 while lo<hi:
  m=(lo+hi)//2
  if active(F(m,100),n,k,j,c,b):hi=m
  else:lo=m+1
 assert active(F(lo,100),n,k,j,c,b)
 return F(lo,100)

if __name__=='__main__':
 n=192
 anchor(n)
 p=poly(n)
 for k in (128,144,160,176,191,192):
  j=min(k+1,n);c=F(p[k],2) if k==n else p[k]
  bb=[bound(b,n,k,j,c) for b in (b0,b2)]
  assert bb[0]>bb[1]
  print('order',k,'exact' if k<n else 'half','B0 and D02 hundredths',
        *[int(x*100) for x in bb],flush=True)
