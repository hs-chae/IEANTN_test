"""Real finite joins and obstructions from the replayed mertens.cc output."""
from cert import F,I,exp,ln
import sys
from pathlib import Path
rows=Path(sys.argv[1] if len(sys.argv)>1 else 'mertens.out').read_text().splitlines()
D=int(rows[0].split()[-1]);assert D==2**56
def iv(a,b): return I(F(a,D),F(b,D))
g0,g1,m0,m1,b0,b1=map(int,rows[1].split())
g,m,b=iv(g0,g1),iv(m0,m1),iv(b0,b1)
w={}; joins={}
for l in rows[2:]:
 if l.startswith('witness'):
  n,rec=l.split(': ');w[int(n.split()[-1])]=list(map(int,rec.split()))
 else:
  c,rec=l.split('/1000: joins ');join,flag=rec.split('; flags ')
  j,k=[int(z) for z in join.split()],[int(z) for z in flag.split()]
  assert len(j)==len(k)==3 and all(1000<=x<=250000000 and x>y for x,y in zip(j,k))
  joins[int(c)]=j
assert joins[200][:2]==[2278383,2278382] and joins[300][2]==912560
# The last line for each witness integer is its value including that integer.
# Same certified fixed prime sums on the real test cell, no internal prime.
def value(n,x,k):
 v=ln(I(x))
 _,_,_,_,a,A,q,Q,s,T=w[n]
 if k=='H':err=iv(a,A)-m-ln(v)
 if k=='Q':err=exp(iv(q,Q)-g-ln(v))-1
 if k=='P':err=1-exp(g+ln(v)-iv(q,Q))
 if k=='S':err=iv(s,T)+b-v
 return err*v**(2 if k=='S' else 3)
for k,n,x,y,c in [('H',2278382,'2278382.111','2278382.115','.2'),
                  ('Q',2278381,'2278381.70','2278381.73','.2'),
                  ('P',2278381,'2278381.56','2278381.59','.2'),
                  ('S',912559,'912559.996','912559.998','.3')]:
 a,d=value(n,x,k),value(n,y,k)
 assert a.above(c) and d.below(c) and d.above(0),(k,str(a),str(d))
 print(k,x,y,c,'opposite signs; same prime-count cell')
# Actual obstructions to carrying lower coefficients back to source onsets.
for k,n,c in [('H',2278383,'.199'),('Q',2278382,'.199'),('S',912560,'.299')]:
 assert value(n,n,k).above(c)
 print(k,n,'normalised absolute error >',c)
