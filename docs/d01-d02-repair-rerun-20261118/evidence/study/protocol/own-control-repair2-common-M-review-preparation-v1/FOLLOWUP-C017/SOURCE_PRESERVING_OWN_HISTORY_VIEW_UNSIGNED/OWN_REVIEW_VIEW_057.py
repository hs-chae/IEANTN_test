from pathlib import Path
from decimal import Decimal as D
import re,sys,json
sys.path.insert(0,'/work/c017')
from profiles import *
from mertens import prime_powers
orig=Path('/corpus/originals')
def lines(name,a,b):
 return next(orig.glob(name+'*.txt')).read_text().split('\n')[a-1:b]
def dec(x):return D(x.replace(' ','').replace('−','-'))
def tab(name,a,b,w):
 s=lines(name,a,b)
 assert len(s)%w==0
 return {(10**int(z[0][1:]) if name=='FKS' and a==2593 and z[0] in ('106','107','108','109') else int(z[0].replace(' ',''))):z[1:] for i in range(0,len(s),w) for z in [s[i:i+w]]}
du={}
for a,b in [(489,728),(742,765)]:du.update(tab('Dusart',a,b,6))
pt=tab('PlattTrudgian1809',142,201,6)
fk=tab('FKS',2317,2575,7)
ft=tab('FKS',2593,2747,5)
for row in SOURCE_DATA['steps']:
 u,v,s=row
 t=du if s.startswith('Dusart') else pt if s.startswith('PT') else fk if 'Table5' in s else ft
 vv=dec(t[u][-1 if t is not ft else 2].replace(' · 10','E').replace('−','-'))
 if vv!=D(v):print('STEP transcription differs:',row,'source',vv)
for row in SOURCE_DATA['shapes']:
 u,A,B,C,R,s=row
 if s.startswith('PT'):
  assert tuple(map(D,(A,B,C,R)))==tuple(map(dec,pt[u][1:4]+['5.573412']))
 elif 'Table6' in s:
  assert tuple(map(D,(A,B,C,R)))==tuple(map(dec,[ft[u][0],'1.5','2','5.5666305']))
 else: assert tuple(map(D,(A,B,C,R)))==(D('9.22022'),D('1.5'),D('.8476836'),D(1))
print('checked 122 steps and 42 shapes from pinned text')
u=I(85)
print('Example of redundant table bound: CH2 at 85 and decreasing thereafter:',sourcefloor+I('113.67')*ef(I('.5'),u))
w=I(32)
l=w*ef(1,w)/2+12*fact[21]/w**21
r=rem(w)
assert (l-r).l>0
print('R2 left-minus-right remainder at L=32:',l-r)
u=I(167); a=I(5)/32
extra=I('1.212')*ef(I('.5')-a,u)+21/I(H)+3*ef(1-a,u)
bound=(I('.276')+extra)*(I('.277')*ef(a,u)/u).exp()
assert bound.r<D('.277')
print('power at [167,170], upper C:',bound)
print('ratio at 200:',I('.234')/I('.0132')*ef(I(1)/32,I(200)))
# Ensure the finite and power rows in the evaluator exactly match the logged computations.
P=json.loads(Path('/work/c017/portfolio.json').read_text())
for k,m,b,c in P['ramanujan_high']:
 from certify import P as test
 assert test(b,basecap,int(k),m) and test(c,newcap,int(k),m)
for u,p,q in P['mertens_power_log_onsets']:
 if u==167:continue
 for b,C in [(basecap,p),(newcap,q)]:
  v=I(u); a=1-I(b)/800
  r=mini(spectral(v,b),continuous_spectral(v,b))/ef(a,v)
  t=I('1.212')*ef(I('.5')-a,v)+21/I(H)+3*ef(1-a,v)
  assert ((r+t)*(I(C)*ef(a,v)/v).exp()).r<D(C)
print('all portfolio.json higher R rows and M power rows checked')

from finite_joins import nxt
import ast
s=Path(__file__).with_name('replay_finite_mertens.py.txt').read_text()
prefix,rest=s.split('Last unproved endpoints (including one-sided prime limits)\n')
raw,tail=rest.split('Endpoint maxima rounded upward to 0.000001\n')
last={}
for r in raw.strip().splitlines():
 c,ls=r.split(' ['); last[D(c)]=ast.literal_eval('['+ls)
def values(r):
 return list(map(D,re.findall(r"Decimal\('([^']+)'\)",r)))
queries={D(r.split()[2]):values(r) for r in prefix.splitlines() if r.startswith('threshold value ')}
maxes={D(r.split()[0]):values(r) for r in tail.strip().splitlines()}
roots={}
fn=Path(__file__).with_name('replay_finite_zoom.py.txt')
for i,r in enumerate(fn.read_text().splitlines()):
 a,b=map(D,r.split('root bounded by ')[1].split()[:2]); roots[i]=(a,b)
for i,x,c in P['mertens_finite_x']:
 X,C=D(x),D(c)
 assert C>=D('.117') or (i<3 and C>=D('.10994'))
 if X>=25000000: continue
 if X in maxes and X in queries and max(maxes[X][i],queries[X][i])<C: continue
 if any(t<=C and nxt(z[i])<=X for t,z in last.items()):continue
 if X in queries and queries[X][i]<C and any(t<=C and z[i]<X for t,z in last.items()):continue
 if X==D(('2278381.575555466','2278381.71114184102','2278382.113038','912559.997437')[i]):
  t=D('.3' if i==3 else '.2')
  assert C==t and last[t][i]<roots[i][0]<roots[i][1]<X
  continue
 raise AssertionError((i,x,c))
print('checked strict finite certificate inputs and sufficient analytic coefficient for all',len(P['mertens_finite_x']),'finite-to-tail rows')
