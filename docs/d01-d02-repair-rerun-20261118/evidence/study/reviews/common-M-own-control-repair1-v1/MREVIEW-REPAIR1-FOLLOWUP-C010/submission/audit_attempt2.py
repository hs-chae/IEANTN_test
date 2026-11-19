#!/usr/bin/python3.10
"""Independent arithmetic spot anchors only; whole-ray justifications in review.md.
Usage: /usr/bin/python3.10 -B audit.py /work/exact_c010
"""
import sys, json, hashlib
from pathlib import Path
p=Path(sys.argv[1])
sys.path.insert(0,str(p))
from bounds import *
from advance import BS4, d_fine, d_light, d_split, point
from repair import shape
from decimal import __libmpdec_version__
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
ix=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for row in ix['candidate_files']:
    assert sha(p/row['original_name'])==row['sha256']==sha(Path('/task')/row['packet_name'])
print('Candidate hashes matched',len(ix['candidate_files']))
ix=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
for row in ix['sources']:
    for ext in ('pdf','text'):
        assert sha(Path(ix['root'])/row[ext])==row[ext+'_sha256']
print('Original PDF and extraction hashes matched',2*len(ix['sources']))
print('Python and libmpdec',sys.version.replace('\n',' '),__libmpdec_version__)
for name,orig in [('bounds','replay.txt'),('finite','finite_replay.txt'),('repair','repair_replay.txt'),('advance','advance_replay.txt')]:
    path=Path(__file__).parent/(name+'.stdout')
    assert path.read_bytes()==(p/orig).read_bytes()
    assert not path.with_suffix('.stderr').read_bytes()
    print(name,sha(path),len(path.read_bytes()))
L=I('168.745')
def floorpow(l):return Q('.0104')*(-I(l)/8).exp()
assertlt(floorpow(190),Q('1.046e-12'))
assertlt((-I(170)/8).exp()*Q('.0104'),Q('8.743e-12'))
for l,z in [(1500,'2.358e-20'),(1000,'6.78e-29'),(1000,'9e-29'),(10000,'3.95e-359')]:
    assertlt(floorpow(l),Q(z))
# All inverse-power comparison shapes: on L>=168.745 log derivatives
# of ratios to exp(-L/8) are positive for k<=4.
for k,c in [(0,1),(1,'.001'),(2,'.01'),(3,'.5'),(4,'151.3')]:
    assertlt(floorpow(190),I(c)/I(190)**k)
    assertlt(Q('1.046e-12'),I(c)/I(190)**k)
x=I(1000); R=I('5.5666305')
assertlt(floorpow(1000),(x/R)*(-(x.ln()/2).exp()).exp())
# Crude normalized PT lower shape: A>1, B>1, C<2, 5<R<6.
assertlt(floorpow(1000), (x/6)*(-((x/5).ln()/2).exp()*2).exp())
for j in (0,1):
    # L/3 initial height conditions, and no escaped finite range
    l=I(40); t=(l/3).exp()
    assertlt(51,t); assertlt(5*t+2,(l/2).exp())
    assertlt(58,(I('2.169e25')).ln())
    assertlt(1,(h/2).exp())
    assertlt(h*h/(8*PI),I('114.671001'))
    assertlt(0, I(cs[13]))
assert all(c>=0 for c in cs[:14])
assert len(cs)==37
assertlt(Q('.19')+Q('.002'),720*(1/I(3914)+196/I(3914)**2))
for x in ('2','2.1','2.29012','2.29014'):
    u=I(x)
    print('shape minus actual absolute psi error, x=',x,shape(u.ln())-(1-LN2/u))
gap=E*I('38358837682.217926')/I('38358837682.217926').ln()*632207037-1644673232**2
assertlt(gap,0)
print('real PT counterexample from locked sieve counts:',gap)
print('PT (18) discrepancy at 2.9:', (1-LN2/I('2.9'))-(1-LN2/2))
g=point(2,'168.72',1,d_fine,True); assertlt(g,81)
print('only constructed refined profile <81 at 168.72:',g)
print('source and analytic anchor checks passed')
