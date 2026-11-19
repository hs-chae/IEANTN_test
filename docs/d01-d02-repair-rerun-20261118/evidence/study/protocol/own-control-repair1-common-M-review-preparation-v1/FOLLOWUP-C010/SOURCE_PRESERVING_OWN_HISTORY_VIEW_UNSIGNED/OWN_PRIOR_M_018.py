#!/usr/bin/python3.10
"""Ancillary checks of exact source identity, endpoint failures, and matched comparison.
No altered analytic algorithm or parameter search. Run with -B from any cwd.
"""
from pathlib import Path
import sys, hashlib, json
import decimal
task=Path('/task'); originals=Path('/corpus/originals')
candidate=Path('/work/review_candidate')
sub=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for row in json.loads((task/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
    p=task/row['packet_name']; h=sha(p)
    assert h==row['sha256']==sha(candidate/row['original_name'])
    print(p.name,row['original_name'],h)
for row in json.loads((task/'SOURCE_INDEX.json').read_text())['sources']:
    for kind in ['pdf','text']:
        p=originals/row[kind];h=sha(p);assert h==row[kind+'_sha256'];print(p.name,h)
print(sys.version, decimal.__libmpdec_version__)
for kind,orig in [('bounds','replay.txt'),('finite','finite_replay.txt')]:
    p=sub/(kind+'.stdout.txt')
    assert p.read_bytes()==(candidate/orig).read_bytes()
    assert (sub/(kind+'.exit.txt')).read_text().strip()=='0'
    assert not (sub/(kind+'.stderr.txt')).read_bytes()
    print(p.name,'byte-identical',sha(p))
sys.path.insert(0,str(candidate))
import bounds as b
from bounds import I,Q,assertlt
L=b.LN2
rad=2*(I('1.5')*L.ln()-I('.8476836')*(L.ln()/2).exp()).exp()
psi_rel=1-L/2
assertlt(rad,psi_rel)
print('FKS Lemma 5.2, x=2: stated radius, true error',rad,psi_rel)
for t in ['1.1','2.1']:
    x=I(t);L=x.ln()
    rad=2*(I('1.5')*L.ln()-I('.8476836')*(L.ln()/2).exp()).exp()
    v=I(1) if x.r<2 else 1-b.LN2/x
    assertlt(rad,v);print('FKS at',x,rad,v)
x=I('2.9')
a=1-b.LN2/2
f=1-b.LN2/x
assertlt(a,f)
print('PT Section 5 (18), x=2.9: assigned radius, true theta error',a,f)
x=I(100)
d=I('113.67')*(-x/2).exp()/(2*b.A_C(x))
assertlt(I('1e-8'),d);assertlt(d,I('1e-7'))
print('Spectral C absolute log derivative at L=100',d)
for x in ['38358837682.217926','38358837682.217927']:
    t=I(x);v=b.E*t/t.ln()*632207037-1644673232**2
    assertlt(v,0) if x.endswith('926') else assertlt(0,v)
    print('PT literal endpoint gap',x,v)
print('matched L=200 power row ratio',I('.256857')/I('.018312')*(-I(200)/32).exp())
print('matched density-free L=300 ratio',(-I(300)/32).exp())
L=I('168.718')
def e(l,upper_side):
    u,w=b.improved_parts(l.l,1,False)
    if upper_side: return b.imin(b.bC(l),b.bD(l,1),u-I('.9999')*(-l/2).exp())
    return b.imin(b.bC(l),b.bD(l,1),w)
p=b.resmain(L,L,2)-b.loss(L,L,e(L,True),e(L-1,False),2)
assertlt(p,81)
print('Failed proposed coefficient 81, signed mesh R5 profile at same L',p)
assertlt(I('1e9'),I(29).exp());assertlt(b.H,I(29).exp())
print('exp(29), exp(17.8), exp(58)',I(29).exp(),I('17.8').exp(),I(58).exp())
# Numerical anchors to the algebraic ratio/floor argument (no domain sampling).
f=lambda L: b.imin(I('1.046e-12'),I('.0104')*(-I(L)/8).exp())
for L,lo in [(16882*Q('.01'),'8.743e-12'),(1500,'2.358e-20'),(1000,'6.78e-29'),(1000,'9e-29'),(10000,'3.95e-359')]:
    assertlt(f(L),I(lo));print('step lower anchor',L,f(L),lo)
for k,eta in enumerate(['.77','.85','1.66','8.16','59.18']):
    assertlt(I('1.046e-12'),I(eta)/I(190)**k)
    assertlt(I('.0104')*(-I(190)/8).exp(),I(eta)/I(190)**k)
for k,eta in {0:'1',1:'.001',2:'.01',3:'.5',4:'151.3'}.items():
    assertlt(I('1.046e-12'),I(eta)/I(190)**k)
    assertlt(I('.0104')*(-I(190)/8).exp()+3*(-I(190)/2).exp(),I(eta)/I(190)**k)
assertlt(I('1.046e-12'),I('.0001')/I(190)**2)
assertlt(I('1.046e-12'),2*(I('1.5')*I(168).ln()-I('.848')*(I(190).ln()/2).exp()).exp())
# For exp(-sqrt(L)) conservative lower bounds, handle the L=190 plateau
# endpoint and then use 1/8-1/(2sqrt L)>0 on each applicable ray.
for LL in [190,1000]:
    L=I(LL)
    assertlt(f(LL),(-(L.ln()/2).exp()).exp())
print('old-source floor anchors verified')

# Ancillary comparison of PT (19),(20) at the published anchor.
# This checks numerical inequalities in the accompanying review derivation.
from math import factorial
t=I(3914)
a=t**5*I('379.7')*(I('1.52')*(t/I('5.573412')).ln()-I('1.89')*((t/I('5.573412')).ln()/2).exp()).exp()
assertlt(1,a)
s=I(3800);R=I('5.573412')
assertlt(I('1.89')/(2*((R*s).ln()/2).exp()) + 7/s,I('.01'))
early=I('2e10')*t**6*(-I(114)).exp()
B=1/t+I(196)/t**2 # underestimates the printed 7*2^8 term
assertlt(a/(I('.99')*t)+early,a*B)
assertlt(I('.19'),720*B)
err=(b.bD(t.l,0,True)+b.err(t))*t**5
assertlt(err+sum(factorial(k)/t**(k-5) for k in range(6,21)),I('.19'))
assertlt(t**6*b.bD(t.l,0,True),720)
print('PT printed anchor comparisons: a, C2 lower magnitude allowance, aB, .19 upper check',
      a,a/(I('.99')*t)+early,a*B,err+sum(factorial(k)/t**(k-5) for k in range(6,21)))

# Safe restriction of the defective small-x FKS statement, keeping its
# later original numerical epsilon bounds exactly where quoted.
def fks52(L):
    return 2*(I('1.5')*L.ln()-I('.8476836')*(L.ln()/2).exp()).exp()
for L,e0 in [(I(3).ln(),'.77'),(I(40),'.77'),(I(1000),'1.93378e-8'),(I(2100),'1.94751e-12')]:
    val=fks52(L);assertlt(I(e0),val);print('FKS restricted-domain anchor',L,e0,val)
