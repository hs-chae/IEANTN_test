"""Closed interval connections to the Taylor rays."""
from cert import I,F,S,exp,err,U,a as plateau
from early2 import check,test
from higher2 import poly,Q,active
from spectral import b0,b2,profile,ceil
from functools import lru_cache

def short_plateau(y):
 t=I(y);w=t-20
 return (plateau*(1+1/(t*(1-2/w)))+
         I(115)*exp(-t/2)*(1+1/(t*(I(F(1,2))-2/w)))+
         t*exp(-20)*(2*plateau/w**2+345*exp(-w/2)/w**2+2000000*exp(-w)))

@lru_cache(None)
def Qmore(y,b):
 p=Q(y,b)
 for v in (168,188):
  if y>=v:p=min(p,ceil(profile(v,b)[-1],10**8))
 return p

def grid(a,b,c,be,k=6,step=F(1,10)):
 L=F(a);B=F(b);p=poly(16)
 assert L>=58
 def cell(L,R):
  l=I(L);u=I(R);v=l-1
  def ru(y,hi,pos):
   e=err(I(y),hi,pos)
   if y>=100:
    w=Qmore(y,be)*exp(-(1-be)*I(y))
    return min(e,w,short_plateau(y),key=lambda t:t.b)
   return e
  rp=ru(L,R,True);rm=ru(L-1,R-1,False)
  cost=u**k*(l/v*rm+(2*U(l)+rp)*rp)
  res=p[k]+sum(p[i]/(u if p[i]>=0 else l)**(i-k) for i in range(k+1,len(p)))
  if (res-cost-I(c)).above(0):return 1
  assert R-L>F(1,10000),(L,R,c,be,k,str(res-cost))
  M=(L+R)/2
  return cell(L,M)+cell(M,R)
 count=0
 while L<B:
  R=min(B,L+step)
  count+=cell(L,R);L=R
 print('closed higher',be,a,b,k,c,count,flush=True)

if __name__=='__main__':
 test()
 for lo,hi,c,side in [
  ('36.688','36.70','.001',True),('36.692','36.70','.003',True),
  ('36.694','36.72','.004',True),('36.712','36.74','.013',True),
  ('36.715','36.74','.014',True),('36.772','36.80','.040',True),
  ('36.780','36.88','.043',True),('36.863','37','.080',True),
  ('36.98','39.47','.137',True),('37.02','39.47','.155',True),
  ('37.05','39.47','.163',True),('39.46','39.47','.885',True),
  ('39.47','40','.163',False),('42.615','42.65','1',False),
  ('48','55.5','1.305',False),('49','54','1.31',False),('50','52','1.32',False)]:
  check(lo,hi,c,side,step='.02')
 check('47.15','47.17','1',var='0',step='.01') # string '0' activates 14/L
 for lo,c,j,b in [('47.6',8,191,b0),('48',40,166,b2),('49.2',80,170,b2),
                  ('49.6',F('80.25'),171,b2),('54',145,124,b0)]:
  check(lo,'58','1',var=c,step='.02')
  grid(58,j,c,b)
  if c<145:assert active(j,16,6,7,c,b) or active(j,16,6,6,c,b)
 grid(58,88,poly(16)[7],b0,7)
