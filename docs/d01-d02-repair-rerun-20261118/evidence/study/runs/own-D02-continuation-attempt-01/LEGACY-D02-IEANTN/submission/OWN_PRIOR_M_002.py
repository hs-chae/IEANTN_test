# Rational readbacks of constants and endpoints used in the review.
# After replay.py has restored /work/rv/exact and /work/rv/own.
import sys, hashlib, json
from pathlib import Path
task=Path('/task')
index=json.loads((task/'CANDIDATE_INDEX.json').read_text())
sources=json.loads((task/'SOURCE_INDEX.json').read_text())
for row in index['candidate_files']:
    p=task/row['packet_name']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
for row in sources['sources']:
    for typ in ['text','pdf']:
        p=Path(sources['root'])/row[typ]
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row[typ+'_sha256']
print('verified',len(index['candidate_files']),'candidate payloads and 14 corpus files')
sys.path[:0]=['/work/rv/exact']
from ram_repair import Q, eu, el, logb, wt_refined, theta_new, pl, pu
a=Q(200); d=Q(1,8)
assert 51<a<64*el(d*a)
assert 64*eu(d*a)<(el(a/2)-2)/5
assert d>1/a
assert logb(Q('2.45')*64/(2*pl))[1]<Q('3.22')
assert logb(Q(3*10**12)/(2*pu))[0]>Q('26.89')
assert 1/(2*pl)<Q('.15916')
assert (d*a+Q('3.22'))>Q('26.89')
cap=Q('.15916')*Q('.142')**2+Q('3.7284')/a**2+Q('2.091')/(64*a)+118*eu(-75)/a**2
assert cap < Q('.004') < Q(1,64)
print('redundancy normalized by L**2 e^(-L/8): cap',float(cap))
N=38358837682
A,B=1644673232,632207037
x=N+Q(1,5)
a,b=logb(x)
neglo=el(Q(1))*B*x/b-A*A
neghi=eu(Q(1))*B*x/a-A*A
assert -1220000 < neglo <= neghi < -1200000
print('R(N+1/5) bracketed strictly in (-1220000,-1200000)')
assert 625/Q('.019535') > 31990
for L,K in [(185,'.01973'),(189,'.01938'),(190,'.01929'),(200,'.01853'),(400,'.01345')]:
    assert theta_new(Q(L))<Q(K)
    print('directed refined C* at',L,'strictly less than',K)
assert wt_refined()[-1]==(Q('.87499'),Q('.01045365'))
# Li(2) anchor from the PV series and constant bracket (0,1).
l,u=logb(Q(2))
# log(log 2) lies between log(1/2) and 0; l>log 2 is not needed:
# log l+l exceeds 0 already at 0.69, since exp(-.69)<.69.
assert l>Q('.69') > eu(Q('-.69'))
# For v=log(2)<.7, the series at v is bounded by exp(.7)-1,
# and subtract at least 0.3 from log v.
assert u<Q('.7') < el(Q('-.3')) and eu(Q('.7'))<Q('2.3')
assert Q('-.3')+1+eu(Q('.7'))-1<2
print('checked PV-li(2) offset allowance and endpoint inequalities')
