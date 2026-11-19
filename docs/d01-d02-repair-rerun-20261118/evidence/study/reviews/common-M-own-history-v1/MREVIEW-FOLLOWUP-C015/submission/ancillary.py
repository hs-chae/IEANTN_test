"""Ancillary checks of locked certificates, not alternative core mathematics."""
import hashlib as hs, json, sys
from pathlib import Path
from fractions import Fraction as F
from zipfile import ZipFile
T=Path('/task')
P=Path('/work/c15')
sys.path.insert(0,str(P))
def rd(p):return json.loads(p.read_text())
def check(p,h,n=None):
    b=p.read_bytes()
    assert hs.sha256(b).hexdigest()==h and (n is None or len(b)==n)
    print(p,h,len(b))
for r in rd(T/'CANDIDATE_INDEX.json')['candidate_files']:
    check(T/r['packet_name'],r['sha256'],r['bytes'])
    assert (T/r['packet_name']).read_bytes()==(P/r['original_name']).read_bytes()
for r in rd(T/'SOURCE_INDEX.json')['sources']:
    for k in ['pdf','text']:check(Path('/corpus/originals')/r[k],r[k+'_sha256'])
assert (T/'INPUT_CONTRACT.json').read_bytes()==(P/'INPUT_CONTRACT.json').read_bytes()
for name in ['prior-candidate.zip','prior-review.zip']:
    with ZipFile(P/name) as z:
        print('Historical archive inventory (not mathematical premises):',name)
        for f in z.namelist():print(f,hs.sha256(z.read(f)).hexdigest())
from verify02 import *
for n in ['1','2']:
    print('version',n,sys.version)
n=38358837682; p=n+F(1,8); X=I(p); y=E*X/X.log()*632207037-1644673232**2
assert low(0,y)
print('Quoted PT real endpoint counterexample:',p,'strict negative interval numerators /',S,y.lo,y.hi)
for p,sgn in [(F(164749953357698434483,4294967296),-1),(F(41187488339424608621,1073741824),1)]:
    X=I(p); y=E*X/X.log()*632207037-1644673232**2
    assert low(sgn*y,0)
print('R rational root bracket, explicit endpoint signs passed')
# Direct anchor check, independent of possible additive source convention.
lo=ex(I(8)); a=lo.lo//S
assert a==lo.hi//S
from mertens import sieve
pr=sieve(a)
th=sum(I(p).log() for p in pr)
ei=r.ei(I(8))
anchor=(len(pr)-ei)-(th-lo)/8
assert low(ex(I(4))*(8**2+8)/(8*PI),m.mx(anchor,-anchor))
print('anchor pi',len(pr),'floor',a,'unnormalized joint anchor error',anchor)
assert low(ex(I('6.5')),599) and low(I('2169e22'),ex(I(58)))
assert low(ex(I(13)),10**4) and low(I(10**13),ex(I('29.9')))
assert low(I(10**12+3),ex(I('27.6')))
assert low(I(10**19),ex(I('43.74')))
assert low(ex(I(30)),10**9)
for a,q in [(34,F(1,2)),(34,F(13,20)),(34,F('.55')),(34,F('.60')),(35,F(2,5))]:
    assert low(q*ex(I(a)/2),10**7)
    assert low(H,q*ex(I(29)))
    assert low(ex(I(a)/2),q)
for a,t in [(200,4*ex(I(25))),(100,ex(I(50))/6)]:
    assert low(t,a) and low(t,51) and low((ex(I(a)/2)-2)/5,t)
assert low(10*ex(I(25)),I('2.45')*4*ex(I(25)))
assert low(ex(I(50)),I('2.45')*ex(I(50))/6)
print('source domain guards for anchor, CH2, finite RH and older FKS heights passed')
# Outcome of the *existing* mass minimum, at every actual paired grid node;
# use exact same candidate generators, not a new grid or search.
ss=sorted({s for z in [F('.8')]+offsets+SP_OFF
            for g in [BETA,BETA0] for s in [z]+[1-r for _,r,_ in make_layers(g,z)] if s<BETA0})
assert all(low(major_fks(s),dusart_mass(s)) for s in ss)
print('Dusart strictly wins analytic mass minimum at all',len(ss),'paired grid nodes')
print('terminal rounded mass numerators /',S,L2[-1][0].hi,L0[-1][0].hi)
# A cellwise guard for the cheap finite_m path: thetaCH at 112 and
# monotone remaining corrections bound U on every entire cell by < 1.
X=I(112)
assert low(1,m.thetaCH(X)+(1+1/X)*j_integrated(X,1)+I('1.84')*ex(-X)+I('1.002')*ex(-X/2)+I('2.67')*ex(-2*X/3))
assert low(I('.015')*ex(I(200)/32)/I('.262'),29)
print('positive finite-product conversion denominator; early .262/.015 rows at 200 also improve >29')
assert tail_R(1597,50)
print('extra matched strength check: D02 degree 50 at fixed B0 degree 40 onset 1597')

try:
    r.run('43.74',80,(1,10),1000,whole=False,error=pi_book)
except ValueError as e:
    print('Optional-source 1+10/L connector: failed sufficient cell, not a counterexample',e)
else:
    raise AssertionError('connector unexpectedly passed')
