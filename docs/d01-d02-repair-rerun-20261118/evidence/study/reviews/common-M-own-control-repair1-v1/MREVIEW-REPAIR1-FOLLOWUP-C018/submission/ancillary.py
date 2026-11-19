#!/usr/bin/python3.10
import sys,hashlib,json
from pathlib import Path
p=Path('/work/c018');sys.path.insert(0,str(p))
from ramref import *
from comparison import C_r,cont
from endpoint import point
H=lambda b:hashlib.sha256(b).hexdigest()
J=json.loads((p/'prior-exact.json').read_text())
for r in json.loads((p/'OWN_ORIGINAL_SOURCE_LOCK.json').read_text())['files']:
 assert H(J[r['path']].encode())==r['sha256']
idx=json.loads((p/'OWN_PRIOR_SOURCE_AND_REVIEW_INDEX.json').read_text())
for r in idx['rows']:assert H((p/r['view_payload']).read_bytes())==r['source']['sha256']
print('Own histories: 24 nested original and 47 indexed sources, exact bytes')
P=Path('/corpus/originals')
rows=lambda f,i,j:(P/(f+'.txt')).read_text().split('\n')[i-1:j]
def dec(s):
 if s in ('106','107','108','109'):return D(10**int(s[2:]))
 return D(s.lower().replace(' ','').replace('−','-').replace('·10','e'))
tab=json.loads((p/'source-tables.json').read_text())
for name,f,a,b,k,cols in [('FKS-5','FKS',2324,2575,7,[0,6]),('FKS-6','FKS',2598,2747,5,[0,1]),
 ('PT-1','PlattTrudgian1809.03134v2',142,201,6,[0,2,3,4,5]),
 ('Dusart-1','Dusart2018',489,764,6,[0,5])]:
 r=rows(f,a,b) if name!='Dusart-1' else rows(f,489,728)+rows(f,742,765)
 assert len(r)==k*len(tab[name])
 for i,v in enumerate(tab[name]):assert [dec(r[i*k+j]) for j in cols]==list(map(D,v))
 print('literal table values',name,len(tab[name]))
r=rows('FKS',3169,3258)
for i,(k,v) in enumerate(sorted(ct.items())):
 assert D(k)/1000==dec(r[9*i]) and D(v)>=dec(r[9*i+6]) and dec(r[9*i+8])<5
 print('FKS Table 8 first panel',k,r[9*i+6],v,r[9*i+8])
assert (I(4)*I('6.1727')/I('.19')).b<130
assert (I(4)*I('4.9')*powq(I(3),Q('.68'))/I('.19')).b<220
for i,L,v in [(0,180,'.025'),(1,160,'.431'),(1,200,'.226')]:
 x=pure(L,i,1);assert x.a>D(v)
 print('coarse sufficient coefficient fails target',i,L,v,x)
for i,t,k,d in [(0,'186',1,'39'),(0,'186',1,'80'),(0,'187',1,'42'),(0,'187',1,'82'),
 (0,'150',2,'0'),(1,'150',2,'0'),(1,'168',1,'83')]:
 u=D(t);z=Grem(u,u,i,k)-I(d)/I(u)**(k+1);assert z.b<0
 print('R sufficient slack only',i,t,k,d,z)
assert point('.1').b<0
print('PT literal real witness at 38358837682.1:',point('.1'))
assert I('.01').exp().b<2 and (2*I('.01')*I('.1')*E(I('.1'),Q('.8476836'))).b<D('.002')
L=I('1e-20')
err=2*I('1e-10')+I(56)/3+I('59.18')*(1/(4*I(4)**4)+1/(5*I(4)**5))
assert err.b<20 and (-L.ln()-1).a>45
print('retired W1 bound <20 and true error >45:',err,-L.ln()-1)
u=I(169);g=mn(I('1.047e-12'),I('.005')*E(u,Q(1,8)))
assert ((2*pp(u)+u*E(u,1))/g).b<D('.01')
assert (PIVAL/(HT-1)).a>D('1.047e-12')
assert (I('.228')*E(I(200),Q(1,32))).b<D('.002')
print('real guard and cost',g,2*pp(u)+u*E(u,1))
print('legacy continuous vs mesh at L=180',cont(180,0,1),common(180,0))
for i,v in [(0,'.006740'),(1,'.118072')]:assert C_r(BETA[i]).b<D(v)
u=I(200); g,w,_=grid(BETA[1],745);a=Q(5,32)
coarse=(I('.04')*u*u+13*u+2)*E(u,Q(1,2)-a)+u*u/50*E(u,Q('.255')-a)+sum((c*E(u,BETA[1]-s) for s,c in zip(g[1:],w)),I(0))
assert coarse.b<D('.227')
print('normalized coarse relative bound at L=200 vs direct D02 >=625:',coarse)
