"""Ancillary review checks; execute with /usr/bin/python3.10 -B audit.py /work/review-c005."""
import hashlib, json, re, sys, zlib
from pathlib import Path
from fractions import Fraction as F
from math import factorial, comb
root=Path('/task')
src=json.loads((root/'SOURCE_INDEX.json').read_text())
cand=json.loads((root/'CANDIDATE_INDEX.json').read_text())
restored=Path(sys.argv[1])
for row in cand['candidate_files']:
    raw=(root/row['packet_name']).read_bytes()
    assert raw==(restored/row['original_name']).read_bytes()
    assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
for row in src['sources']:
    for kind in ('pdf','text'):
        assert hashlib.sha256((Path(src['root'])/row[kind]).read_bytes()).hexdigest()==row[kind+'_sha256']
print('25 exact locked candidate files and 14 original PDF/extraction hashes verified')
raw=(Path(src['root'])/'PlattTrudgianFiniteRH.pdf').read_bytes()
page=re.search(rb'(?ms)^112 0 obj\s*(.*?)endobj',raw)[1]
assert b'/Contents 114 0 R' in page
pdf=zlib.decompress(raw[re.search(rb'(?ms)^114 0 obj.*?stream\r?\n',raw).end():])
frag=pdf.split(b'[(li\\()',1)[1].split(b'(2)-2.83652(6)-2.83857(5)-2.83857(7)-2.83857]TJ',1)[0]
assert b'(lo)-2.83857(g)' in frag and b'15.1199 5.16016 Td\n[(2)4.03117]TJ' in frag
print('PT finite RH PDF page 4 object 114: pi row literal log exponent 2 and lower endpoint 2657')
sys.path.insert(0,str(restored))
from certify import E, EP, ex, H, qlt, qc, qa
from mertens_cert import Kt, osc
from edge import cmp
lo,hi=F('3.1415'),F('3.142')
# Machin's formula, alternating enclosure on two arctangent series.
def atan(n,terms):
    return sum((F((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(terms)),F(0))
assert lo <16*atan(5,10)-4*atan(239,11)
assert 16*atan(5,11)-4*atan(239,10)<hi
assert hi/(H)<F('1.048e-12')
assert hi*10**7/(10**7-1)+hi**2/(3*10**7)<F('3.15')
assert 1/(8*lo)<F('.0398')
assert -(F('2.26')/2+F(1,12))/hi < -F('.385')
assert (F('2.27')**2/2+F('2.27')/6)/lo+F('3.15')/F('.65')<F('5.80')
assert F('.65')*EP(29)<H and F('.65')/E(17)>10**7 and 1/E(34)>10**9
assert 1/(18*lo)+F('1.8642')/150**2 < F('.018')
assert F(4,25)/(2*lo)+F('1.8642')/150**2 <F('.026')
assert 5*EP(60)+2<1/E(75) and 1/E(60)>300
assert 5*EP(50)+2<1/E(75) and 1/E(50)>150
# Direct comparison using T=e^(200/6); product form handles both exponentials.
assert 5+2*E(F(100,3))<1/E(F(200,3)) and 1/E(F(100,3))>200
assert 1/E(F('36.85'))>38358837683 and EP(F('36.85'))<F('1.15e16')
assert EP(F('39.47'))<F('1.39e17')
assert EP(F('29.9'))<10**13
assert F(3,100)>0 and F('.0045')<F(1,64)
# c1 strip prefactor inequality after taking fifteenth powers.
assert (2*F('8.162'))**15*F('2.45')**8<40**15
assert 1/(2*lo)+9*E(60)<F('.17')
assert 4*F(2,5)*E(60)<F('.004')
assert EP(F(1,8))<F(4,3)
assert EP(20)<500000000 and 1/E(F('20.1'))>500000000
# Certified concrete counterexample to the printed real PT endpoint; use same verified counts.
B=38358837682
low,high=cmp(B+F(1,8),1644673232,632207037)
assert -10**7<low<high<-10**6
print('PT real counterexample x=38358837682+1/8; -10000000 < R(x) < -1000000')
for j in (150,182,190,194,195,200,250,400,810,1500,3000):
    # Same proposed oscillatory bound, denominator positivity checked separately.
    L=F(j)
    from mertens_cert import osc
    w,d=osc(j)
    assert 0<w<1 and 0<d<1
assert F('.019354')*E(25)<F('1.049e-12')
assert F('.019354')*E(25)*200**2 < F('.0667')
assert F('.019354')*E(25)*200**2 < F('.0726')
assert F('.019354')*E(25)*200**2 < F('.2')
print('Auxiliary exact inequalities for admissibility, normalization, strip and matched comparisons passed')
