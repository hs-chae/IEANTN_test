"""Independent local guards; no new analytic construction or parameter search.
Run with cwd at restored candidate and PYTHONPATH set to that directory.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import ast, json
import d02screen as s
from d02rigor import I, log, exp, PI
import d02ram as r
import d02m as m
from endpoint_check import lu, ei
from mertens_check import sieve, add, lp_data, residuals, B
def D(z): return sha256(z.read_bytes()).hexdigest()
for p in json.load(open('/task/SOURCE_INDEX.json'))['sources']:
    for k in ('pdf','text'):
        assert D(Path('/corpus/originals',p[k]))==p[k+'_sha256']
for p in json.load(open('/task/CANDIDATE_INDEX.json'))['candidate_files']:
    assert D(Path(p['original_name']))==p['sha256']
print('Exact identity: 192 candidate payloads, 14 original-source bindings')
N=38358837682
x=N+F(1,10); lo,hi=lu(x); el,eu=ei(F(1))
P,Q=1644673232,632207037
assert -8100000<el*x*Q/hi-P**2<=eu*x*Q/lo-P**2<-7900000
print('At N+1/10: -8100000 < R < -7900000 (counts from exact quotient replay)')
a=I(20)
assert 2*a*exp(-a/2)/(8*PI)+1354*a*exp(-a)<3*a*exp(10-a)
assert exp(I('26.8'))>2657 and exp(I('29.9'))<10**13 and exp(I('30.8'))<10**19
assert exp(I(34))>10**9
for L,c in [(155,F('.19')),(155,F('.27')),(155,F('.35')),(180,F('.45')),(200,F('.25'))]:
    assert exp(c*I(L))>max(51,L)
    assert 5*exp(c*I(L))+2<exp(I(L)/2)
assert I('113.67')+I('1.000000147')+I('1.78')*exp(-log(2)/6)<117
assert r.ac(6)>F(1,24)*720
print('Earliest shifted prefix, cutoff starts and coefficient endpoint guards passed')
s.prelim()
print('Chosen uniform bins:',len(s.chords()),'out of',len(s.table()))
assert len(s.chords())==479 and len(s.table())==495
for j,c in [(1,I('.116297')),(2,I('2.506e-14'))]:
    w=s.U(s.mass(s.b,j,True))
    assert w<c
    print('Terminal upward Dusart ceiling (m):',j,w)
assert s.U(s.mass(F(7,8),1,True))>I('.00666')
print('B0 full-height CH2 boundary test is in repair_limits.py')
x=912560
sv=sieve(x)
st=(0,)*6
for p in range(2,x+1):
    if sv[p]: st,_,_=add(st,p)
argv=__import__('sys').argv
f=Path(argv[1])
raw=f.read_text().splitlines()[1].split(': ',1)[1]
G,M,C=ast.literal_eval('('+raw.replace(') (','),(')+')')
L=lp_data(x)
l,u=residuals(st,st,L,L,(*M,*C))[2]
assert F('.2999993')<F(l*L[0]**2,B**3)<=F(u*L[1]**2,B**3)<F('.2999995')
print('Weighted benchmark at 912560: .2999993 < L^2 delta_V < .2999995')
from ray_check import grid, loss, TAIL
for a,b,step in [(50,58,F(1,8)),(58,100,F(1,4)),(100,169,F(1,4))]:
    for l,r in grid(F(a),F(b),step):
        assert 85+1412/r-TAIL/l**7>r**6*loss(l,r,'C')
print('Retained QRH-free K=60 on [50,169] independently replayed')
