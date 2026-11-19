"""Ancillary checks for locked methods, not a new parameter search."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,re,sys,zlib
p=Path(sys.argv[1]);sys.path.insert(0,str(p))
from edge import cmp
from density import EL,E
from gap02 import model,basic
root=Path('/corpus/originals')
ix=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for x in ix['candidate_files']:
    data=(p/x['original_name']).read_bytes()
    assert data==(Path('/task')/x['packet_name']).read_bytes()
    assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256']
print('exact member readback:',len(ix['candidate_files']))
pdf=(root/'PlattTrudgianFiniteRH.pdf').read_bytes()
def obj(n): return re.search(rb'\n'+str(n).encode()+rb' 0 obj\b(.*?)endobj',pdf,re.S)[1]
assert b'/Contents 114 0 R' in obj(112)
a=zlib.decompress(obj(114).split(b'stream\n',1)[1])
q=re.search(rb'251\.76 506\.52 Tm(?P<row>.{0,700})',a,re.S)['row']
assert re.search(rb'\(lo\).*?\(g\).*?/R31.*?5\.16016 Td.*?\(2\).*?-5\.16016 Td.*?\(x',q,re.S)
assert re.search(rb'\(2\).*?\(6\).*?\(5\).*?\(7\)',q,re.S)
print('finite RH PDF p4 object112/content114, pi log-squared glyph:', repr(q[:500]))
def atan(x):
    l=sum((-1)**n*x**(2*n+1)/(2*n+1) for n in range(10))
    return l,l+x**21/21
u,v=atan(F(1,5)); w,z=atan(F(1,239))
assert F('3.1415')<16*u-4*z and 16*v-4*w<F('3.142')
for j,k,b in [(200,F(1,6),200),(150,F(1,3),150),(100,F('.47'),100),(150,F(2,5),300)]:
    assert max(51,b)*E(k*j)<1 and 5*E((F(1,2)-k)*j)+2*E(F(j,2))<1
assert F('3.142')/(1-F('1e-7'))+F('3.142')**2/F(3*10**7)<F('3.15')
assert 1/(8*F('3.1415'))<F('.0398')
assert F('2.26')/(2*F('3.142'))+1/(12*F('3.142'))>F('.385')
assert F('2.27')**2/(2*F('3.1415'))+F('2.27')/(6*F('3.1415'))+F('3.15')/F('.65')<F('5.80')
assert (2*F('8.162')/40)**15*F('2.45')**8<1
assert F(1,2)*(1/F('21.1')-F(3,160000))>F(1,44)
assert F(1,2)*(1+F(3,8000))/20*(1+F(1,499999999))<F(1,39)
assert F('1.000375')*(1+F(1,499999999))<F('1.000376')
assert EL(F('21.45'))*2100000000>1 and EL(20)*500000000>1
assert F('.22528')*E(F(200,32))<F('.000435')
assert F('.87')*E(F(181,32))<F('.015')
assert F('.270')*EL(F(20,32))>F('.00141') and F('.270')*E(F(180,32))<F('.00141')
for start,minimum in [(180,'2.536e-12'),(2500,'2.358e-20'),(1000,'6.78e-29'),(1000,'1e-30'),(10000,'1e-359')]:
    assert F('.006')*E(F(start,8))<F(minimum)
print('admissibility, normalization tails, joins and comparison scales checked')
B,n,a,b=map(int,(p/'edge_result.txt').read_text().splitlines()[0].split())
x=F(B)+F(1,8)
lo,hi=cmp(x,a,b)
assert F(-10**7)<lo<=hi<F(-10**6)
print('quoted PT real-range counterexample:',x,'R in (-10000000,-1000000)')
# Upper bound for r using submitted 20-term li expansion and B0 model error.
L=F(10000)
s,_,aL,_=basic(L,20)
sm,rm,_,_=basic(L-1,20)
assert s>aL
upper=L**4*(L/(L-1)*(sm+rm)-(s-aL)**2+F('.048')*E(L/8))
trial=sum(c/L**j for j,c in enumerate([1,14,145,1412,15000]))
assert upper<trial
print('withdrawn fifth coefficient 15000: r < trial at x=exp(10000) (B0)')
