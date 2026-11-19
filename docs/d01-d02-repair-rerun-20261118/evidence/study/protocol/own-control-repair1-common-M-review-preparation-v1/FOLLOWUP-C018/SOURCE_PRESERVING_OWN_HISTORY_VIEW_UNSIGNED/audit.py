#!/usr/bin/python3.10
"""Source and exact historical identity checks; diagnostic failures of sufficient bounds."""
import json,hashlib
from pathlib import Path
from ramref import *
task=Path('/task'); path=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
sindex=json.loads((task/'SOURCE_INDEX.json').read_text())
src=Path(sindex['root'])
for row in sindex['sources']:
 for k in ['text','pdf']:
  assert sha((src/row[k]).read_bytes())==row[k+'_sha256']
print('all original sources byte-matched')
ix=json.loads((task/'OWN_REVIEW_INDEX.json').read_text())
hist=json.loads((path/'prior-exact.json').read_text())
for row in ix['prior_candidate_files']:
 assert sha(hist[row['original_name']].encode())==row['sha256']
print('all historical payloads recoverable byte-for-byte',len(hist))
for row in ix['own_review_files']:
 assert sha((task/row['packet_name']).read_bytes())==row['sha256']
print('all own-feedback files byte-matched')
def rows(n,i,j):
 return (src/(n+'.txt')).read_text().split('\n')[i-1:j]
def dec(x):
 if x in ['106','107','108','109']:return 10**int(x[2:])
 return D(x.lower().replace(' ','').replace('−','-').replace('·10','e'))
tab=json.loads((path/'source-tables.json').read_text())
for name,n,b,e,k,cols in [
 ('FKS-5','FKS',2324,2575,7,[0,6]),('FKS-6','FKS',2598,2747,5,[0,1]),
 ('PT-1','PlattTrudgian1809.03134v2',142,201,6,[0,2,3,4,5]),
 ('Dusart-1','Dusart2018',489,764,6,[0,5])]:
 rr=rows(n,b,e) if name!='Dusart-1' else rows(n,489,728)+rows(n,742,765)
 for i,r in enumerate(tab[name]):assert [dec(rr[i*k+j]) for j in cols]==list(map(D,r))
 print('literal table',name,len(tab[name]))
rr=rows('FKS',3169,3258)
for i,(k,v) in enumerate(sorted(ct.items())):
 assert D(k)/1000==dec(rr[9*i]) and D(v)>=dec(rr[9*i+6]) and dec(rr[9*i+8])<5
 print('literal density bin',k,rr[9*i+6],v)
assert (I(4)*I('6.1727')/I('.19')).b<130
assert (I(4)*I('4.9')*powq(I(3),Q('.68'))/I('.19')).b<220
assert I('.01').exp().b<2
assert (2*I('.01')*I('.1')).b<1
L=I('1e-20')
e=2*I('1e-10')+I(56)/3+I('59.18')*(1/(4*I(4)**4)+1/(5*I(4)**5))
assert e.b<20 and (-L.ln()-1).a>45
print('original ungated source and transfer are counterexamples, not active branches')
for i,a,k,d in [(0,'150',2,'0'),(1,'150',2,'0'),(1,'168',1,'83'),(0,'187',1,'42')]:
 t=D(a);z=Grem(t,t,i,k)-I(d)/I(t)**(k+1);assert z.b<0
 print('refined R sufficient test fails',i,a,k,d,z)
for i,t,v in [(0,180,'.025'),(1,160,'.431'),(1,200,'.226')]:
 z=pure(t,i,1);assert z.a>D(v)
 print('corrected coarse M sufficient test fails; replaced by stratified proof',i,t,v,z)
