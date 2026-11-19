# Ancillary check of the submitted interfaces; no new arithmetic portfolio.
from pathlib import Path
import sys,json,hashlib
sys.path.insert(0,'/work/review-input')
from dyad import I,F,PI,exp,ln
from spectral import cap,terms,cutoffs,b0,b2
from refine2 import fine_cap
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
for s in json.loads(Path('/task/SOURCE_INDEX.json').read_text())['sources']:
 for k in ('pdf','text'): assert sha(Path('/corpus/originals',s[k]))==s[k+'_sha256']
 print(s['source_id'],s['pdf_sha256'],s['text_sha256'])
for b in (b0,b2):
 K,a=cap(b);J,d=fine_cap(b)
 def B(z,k,p):
  return k+sum(m*max(0,u-max(l,z)) for l,u,m in p)
 xs=sorted({F('.70'),b}|{j for l,u,_ in a+d for j in (l,u)})
 assert all(B(z,J,d)<=B(z,K,a) for z in xs)
 print('fine <= coarse continuous linear cap on all cells, b and number of endpoints',b,len(xs))
 for k,j in cutoffs:
  assert all(mu>F('1/100') for _,_,mu in terms(100,b,k,j))
  assert (exp(1)-I('2.45')).above(0)
  P=list(terms(200,b,k,j))
  print('cutoff, b, count of residual terms',k,j,b,len(P))
x=I(F(10000001,10000000));v=ln(x);sqrtx=exp(v/2)
T=2*PI**2*sqrtx/v
bound=sqrtx*v**2/(8*PI)
assert T.above(10**7) and T.below(3*10**12) and bound.below('1e-13')
assert x.below(2) and (x-bound).above(1)
print('CH2 9.3 literal low branch counterexample x=1.0000001',T,bound)
from cert import I as C,exp as ce,ln as cl
import compare2 as cp
from joins2 import short_plateau
from repair_cert import qscaled
from spectral import profile
for b in (b0,b2):
 for y in (164,165):
  w=C(y);p=profile(y,b)[-1]*exp(-(1-b)*I(y))
  vals=[cp.lift(cp.ch(w)),cp.lift(short_plateau(y)),cp.lift(qscaled(w)*ce(-w/8)),cp.lift(cp.qr(w)),p]
  assert vals[1].b<min(v.a for i,v in enumerate(vals) if i!=1)
print('short plateau wins both shifted and unshifted arguments for both b at L=165')
# Exact M-plateau/polynomial matched comparison.
r=I('.00049')*exp(-25)
assert r.below('1.05e-12') and (200**2*r).below('.0378')
assert F('.00049')*20<F('.010443618317')
assert ((1+F(2,3*10**12))*F('.010445')==F(3133500000002089,300000000000000000))
print('plateau/poly and limit comparisons')
