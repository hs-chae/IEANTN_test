"""Review-only exact identity / endpoint checks, with no parameter search."""
import json,sys
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as Q
packet=Path('/task')
restored=Path(sys.argv[1] if len(sys.argv)>1 else '/work/locked')
def hd(p):return sha256(p.read_bytes()).hexdigest()
for row in json.loads((packet/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
    assert hd(restored/row['original_name'])==hd(packet/row['packet_name'])==row['sha256']
for row in json.loads((packet/'OWN_HISTORY_DISCLOSURE.json').read_text())['candidate_history_files']:
    assert hd(packet/row['packet_name'])==row['sha256']
for row in json.loads((packet/'SOURCE_INDEX.json').read_text())['sources']:
    for fmt in ('pdf','text'):
        assert hd(Path('/corpus/originals')/row[fmt])==row[fmt+'_sha256']
print('candidate, historical copies, and all 14 original PDF/text digests verified')
sys.path.insert(0,str(restored))
from d02_density_new import nodes,mass,D,D0,el,eu,F,J,pl,pu
import d02_ram_new as R
import d02_m_new as M
import ram_repair as O
assert [s for s in nodes(D0) if s<=1-D]==nodes(D)
for m in (1,2):
    assert mass(D0,m)[:len(nodes(D))]==mass(D,m)
    assert mass(D0,m)[-2][1]>0
print('identical shared mesh and transfer weights through 27/32',len(nodes(D)),len(nodes(D0)))
assert mass(D0,1)[-2][1]>Q('.01044')
assert min(O.WTS[-1][1], O.wt_refined(False)[-1][1], O.wt_refined(True)[-1][1])>Q('.01044')
assert Q('.300102')*eu(-Q(169,32))<Q('.001527')
assert Q('.300102')*eu(-Q(845,32))<Q('9.22022')*169*13*el(-Q('.8476836')*13)
assert el(Q('27.704'))>10**11 and eu(Q('27.704'))<Q('1.15e16')
assert eu(Q('43.7'))<10**19 and eu(Q(58))<Q('2.169e25')
h=3000175332800
assert pu/(h-1)+(pu/h)**2 < Q('1.047136353e-12')
print('CH2 corrected denominator H-1 leaves written q valid')
assert el(Q('59.99'))>max(3000175332800,10**9)
# Finite profile certificate joins to stronger inherited tails, not a new search.
assert O.tail(Q(288),9,0,True)>0
assert Q(1)+Q(14,388)+Q(145,388**2)>Q('1.037')
assert Q(1)+Q(14,221)+Q(16,221**2)>Q('1.037')
print('full-ray join constants verified')
# Re-run selected rejected trials as sufficient-check diagnostics only.
for t in [('49.4',172,6,'80.8'),('49.4',172,6,81)]:
    ok,n,s,a,b=R.adapt(*t,panels=128,depth=19)
    print(t,ok,n,float(s),str(a),str(b)); assert not ok
for A,j in [('186.5',7),('534.9',20)]:
    r=R.end(A,j,0,20)
    print('rejected fixed-order endpoint',A,j,float(r/R.polys(20)[0][j])); assert r<0
A=Q('189.12')
v=O.rem(A,A,6)-R.cost(A,A,6,D0,128)
print('B0 rational sufficient test at L=189.12, z allowance',float(v)); assert v<Q('80.6')
assert M.logray('61','2.9871e-8','168.901',verify=False)>Q('2.9871e-8')
t=M.under('87.2')
print('87.2 positivity sufficient test',float(t)); assert t<0
