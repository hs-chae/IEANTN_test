from pathlib import Path
import hashlib as h, json, re, sys
from decimal import Decimal as D
T=Path('/task'); CORPUS=Path('/corpus/originals'); base=Path('/work/review-c018')
sys.path.insert(0,str(base))
from verify import *
from mertens import pure
from comparison import cont
for r in json.loads((T/'SOURCE_INDEX.json').read_text())['sources']:
 for k in ['pdf','text']:
  p=CORPUS/r[k]
  import hashlib
  a=hashlib.sha256(p.read_bytes()).hexdigest()
  assert a==r[k+'_sha256']; print(p.name,a)
def sle(n,i,j):
 return (CORPUS/(n+'.txt')).read_text().split('\n')[i-1:j]
def ds(x):
 if x in ['106','107','108','109']: return D(10)**int(x[2:])
 return D(x.lower().replace(' ','').replace('−','-').replace('·10','e'))
tab=json.loads((base/'source-tables.json').read_text())
for name,n,i,j,step,cols in [
 ('FKS-5','FKS',2324,2575,7,[0,6]),('FKS-6','FKS',2598,2747,5,[0,1]),
 ('PT-1','PlattTrudgian1809.03134v2',142,201,6,[0,2,3,4,5]),
 ('Dusart-1','Dusart2018',489,764,6,[0,5])]:
 raw=sle(n,i,j)
 if name=='Dusart-1':raw=sle(n,489,728)+sle(n,742,765)
 for k,row in enumerate(tab[name]):
  o=[raw[k*step+x] for x in cols]
  got=[ds(s) for s in o]; assert got==list(map(D,row)),(name,k,got,row)
 print('matched',name,len(tab[name]))
for k,(a,b) in enumerate([(1,'M'),(2,'M-ram'),(4,'R'),(5,'R-ram'),(9,'comparison'),(12,'diag'),(14,'endpoint'),(16,'finite'),(19,'high'),(20,'high-ram')]):
 q=json.loads(Path('/work/submission',f'replay-{b}.json').read_text())
 match=q['stdout'].encode()==next(T.glob(f'CANDIDATE_{a:03d}.*')).read_bytes()
 print('byte match',b,match);assert match
v=I('.21792636'); x=I(38358837682)+v
assert (I(1).exp()*x/x.ln()*632207037-1644673232**2).b<0
assert I('.01').exp().b<2 and (2*I('.01')**1*I('.1')).b<1
print('counterexample FKS Lemma 5.2, x=e^.01: Epsi=1 > RHS (RHS < .002)')
print('counterexample literal PT Thm 2, x=38358837682.21792636')
assert (I('27.6').exp()).b<10**12+3
assert (I(599)/I(2).ln()**2+2/I(2).ln()).b<1255
assert I('16.8').exp().b<2*10**7<I('16.82').exp().a
N=2*10**7
low=(1-1/I('16.8')-I('.001')*(3+1/I('16.8')))/(2*N*I('16.82'))
high=(1+I('.001')*(3+1/I('16.8')))*(1+I(2)/N)/(2*N*I('16.8'))
assert low.a>D('1.38e-9') and high.b<D('1.50e-9')
assert (I('3.01e12')-H).a>0
assert (I(2)*5*2/I('.19')).b<106
assert (I(2)*I('4.9')*(I(3).ln()*I('.68')).exp()*2/I('.19')).b<220
assert (I('.228')*E(I(200),Q(1,32))).b<D('.002')
for cap,val,L,target in [(0,'.0142',224,'1e-14'),(1,'.242',198,'1e-14'),(0,'.0111',296,'1e-18'),(1,'.193',255,'1e-18')]:
 assert (I(val)*E(I(L),1-BETA[cap])).b<D(target)
print('RAM_ONLY target examples still hold at 224/198 and 296/255')
for cap,L,s in [(0,180,'.025'),(0,190,'.0161'),(0,200,'.0135'),(0,210,'.0126'),(0,220,'.012'),(1,160,'.431'),(1,170,'.302'),(1,180,'.258'),(1,185,'.247'),(1,190,'.238'),(1,200,'.226'),(1,210,'.217')]:
 t=pure(L,cap,1)
 if RAM_ONLY: assert t.a>D(s)
 print('substituted mesh certificate',cap,L,s,t)

# An explicit false output of the unguarded minimum/transfer recipe itself.
L=I('1e-20')
from decimal import Decimal
# u<=4 use 2u^(3/2), for u>=4 use Dusart 3.3 (59.18/u^4).
int_upper=I(56)/3+I('59.18')*(1/(4*I(4)**4)+1/(5*I(4)**5))
gamma_hi=I(1) # elementary 0<=gamma<=1 by harmonic-integral comparison
assert (2*I('1e-10')+int_upper).b<20
assert (-L.ln()-gamma_hi).a>45
print('unguarded psi -> W1 transfer at L=1e-20: radius <20 but W1 >45')

# Additional literal comparison and analytic-side domain constants.
assert (I(2).ln()).a>D('.69')
assert (2*I(10).exp()).a>0
assert (I('39.47').exp()).b<I('1.39e17').a
assert all(I(z).exp().b<20_000_000 for z in ('16.05','16.25','16.45','16.7','15.5','15.65','16','16.5'))
assert I('36.9').exp().b<D('1.15e16')<I('37').exp().a
z=I(200)
assert (I('.04')/z**2).a>(I('.005')*E(z,Q(1,8))).b
assert (I('.001')/z**4).a>(I('.005')*E(z,Q(1,8))).b
print('all 8 finite joins overlap; original-output log guard at 200 checked')

raw=sle('FKS',3169,3258)
for k,(ss,c) in enumerate(sorted(ct.items())):
 row=raw[9*k:9*k+9]
 assert ds(row[0])==D(ss)/1000 and ds(row[8])<5
 ok=ds(c)>=ds(row[6])
 assert ok==(k>=2)
 print('FKS band transcription',ss,'source=',row[6],'candidate=',c,'outward=',ok)
assert (I('.228')/I('.0142')*E(I(200),Q(1,32))).b<D('.033')
for cap in BETA:
 p=Q(8,3)*(1-cap)
 assert (I('4.9')*(f(p)*I(3).ln()).exp()).b<D(ct[max(i for i in ct if Q(i,1000)<=cap)])
 # Verify full min comparison at the cap including additive terms.
 old=RAM_ONLY
 import verify
 verify.dens.cache_clear()
 verify.RAM_ONLY=True
 rr=verify.dens(cap)
 verify.dens.cache_clear()
 verify.RAM_ONLY=False
 assert (rr.a,rr.b)==(verify.dens(cap).a,verify.dens(cap).b)
 verify.dens.cache_clear()
 verify.RAM_ONLY=old
 print('identical Taylor cap evaluation',cap,rr)
