"""Verifier of candidate endpoint/source guards, not a new certificate algorithm."""
import hashlib,json,sys,zipfile
from pathlib import Path
from pdf_readback import get
P=Path('/task'); src=Path('/corpus/originals')
digest=lambda b:hashlib.sha256(b).hexdigest()
assert not sys.flags.optimize
for r in json.loads((P/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
    z=(P/r['packet_name']).read_bytes()
    assert len(z)==r['bytes'] and digest(z)==r['sha256']
    assert z==(Path(sys.argv[1])/r['original_name']).read_bytes()
    print('candidate',r['packet_name'],r['original_name'],r['sha256'])
pages={'CH2':[3,35,36,43],'DudekPlatt2015':[2,8,9,10],'Dusart2018':[3,4,7,8,11,13,14,17,18,19,20],
       'FKS':[2,3,4,5,7,8,22,23,26],'OpenAIQRH':[4],'PlattTrudgian2021':[2,3,10,11],
       'PlattTrudgianFiniteRH':[2,4,5]}
for r in json.loads((P/'SOURCE_INDEX.json').read_text())['sources']:
    for t in ('pdf','text'):
        assert digest((src/r[t]).read_bytes())==r[t+'_sha256']
        print('original',r[t],r[t+'_sha256'])
    for n in pages[r['source_id']]:
        k,v,c,_=get(str(src/r['pdf']),n)
        print('PDF original page',r['source_id'],n,'page object',k,'content objects/digests',[(i,digest(z)) for i,z in c])
with zipfile.ZipFile(P/'CANDIDATE_018.zip') as z:
    for f in json.loads((P/'CANDIDATE_017.json').read_text())['files']:
        assert digest(z.read(f['path']))==f['sha256']
with zipfile.ZipFile(P/'CANDIDATE_019.zip') as z:
    book=json.loads(z.read('OWN_REVIEW_INDEX.json'))
    for f in book['own_review_files']:
        d=z.read(f['packet_name'])
        assert digest(d)==f['sha256'] and len(d)==f['bytes']
    assert z.read('OWN_REVIEW_006.stdout')==(P/'CANDIDATE_016.stdout').read_bytes()
print('own archive bindings PASS')

sys.path.insert(0,sys.argv[1])
from analytic import *
from ramanujan import endpoint
from mertens import test_poly,sieve

def uh(t,L):
    return low(t,max(51,L)) and low((ex(I(L)/2)-2)/5,t)
assert uh(4*ex(I(25)),200) and uh(ex(I(50))/6,100)
assert low(10*ex(I(25)),I('2.45')*4*ex(I(25)))
u=I(10**6).log(); p=(2*PI).log()
c=1/(2*PI)+(I('.137')*u+I('.443'))/(10**6*u*(u-p))
b1=I(23)/200**2+I('.16')*(I(1)/8+I(10).log()/200)**2+I('2.091')/800
assert low(I(1)/160,b1)
print('B0 redundancy coefficient upper interval at L=200:',b1)
assert low(I('2.169e25'),ex(I(58))) and low(ex(I(8)),2657)
assert low(I('1e19'),ex(I('43.74')))
assert low(I('1e13'),ex(I('29.9'))) and low(ex(I(13)),10**4)
for a,ratio in [(34,F(1,2)),(34,F(13,20)),(35,F(2,5))]:
    assert low(ratio*ex(I(a)/2),10**7)
    assert low(H,ratio*ex(I(58)/2))
    assert low(ex(I(a)),10**9) and low(ex(I(a)),ratio*ex(I(a)/2))
assert low(ex(I(30)),10**9) and 10**7<=H
assert low(ex(I('6.5')),599)
assert low(ex(I(100)),767135587)
assert low(I('.001'),I('.5')/100**3)
assert low(I('.0196'),refined(I(200))*ex(I(25)))
assert F(200**2,64)>31000*F('.0196')
for k,c in [(2,'.185'),(2,'.175'),(2,'.09'),(3,'.5'),(4,'4'),(5,'.3')]:
    assert low(I(c),I('.021')*ex(-I(240)/8)*I(240)**k)
assert low(I('.3')*I('.3'),I('.0196')*ex(-I(200)/8)*I(200)**5)
print('height, source guard, polynomial joins and original comparison PASS')
endpoint()
for t,sgn in [(".217926365",-1),(".217926366",1)]:
    y=I(38358837682)+I(t)
    v=E*y*632207037/y.log()-1644673232**2
    assert low(sgn*v,0)
    print('root endpoint decimal offset',t, 'exact sign',sgn, 'scale interval',v.lo,v.hi)
x=I(F(38358837682)+F(1,8))
r=E*x*632207037/x.log()-1644673232**2
assert low(0,r)
print('counterexample to quoted PT real ray at',F(x.lo,S),': scaled exact interval',r.lo,r.hi,'/ SCALE',S)

# Compare raw and normalized meanings at the lower extremum location
# reported by CH2; this is not a re-verification of the CH2 full range.
q=1423
y=gamma()-I(q).log()
for p in sieve(q-1):
    a=p
    while a<q:
        y+=I(p).log()/a
        a*=p
assert low(y,I('-.021')) and low(I('-.019'),y)
w=power(q,F(1,2))*y
assert low(w,I('-.758583')) and low(I('-.758582'),w)
print('CH2 reported 1423-left location: raw D',y,'sqrt(x) D',w)
try:
    test_poly(16,240,[(0,0)]*3+[(2,'.175')])
except ValueError as e:
    print('expected cap-free failure of OLD sufficient certificate:',e)
else:
    raise AssertionError('unexpected pass of old sufficient certificate')
