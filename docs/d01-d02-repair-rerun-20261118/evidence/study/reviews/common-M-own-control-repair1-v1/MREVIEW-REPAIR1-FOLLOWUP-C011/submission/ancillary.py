"""Fixed-parameter checks of declared estimates; no search for new theorems."""
from pathlib import Path
from math import factorial
import sys, re, zlib, hashlib, json
sys.path.insert(0, sys.argv[1])
from intervals import I, F, PI, log, exp
from certificate import CH, fRH, transfer, fu, coefficient, A, H, T0
from source_rows import extract
def ck(a,b): assert I(a).lt(b), (I(a).pt(),I(b).pt())
base=Path('/corpus/originals')
def stream(name,n):
    b=(base/(name+'.pdf')).read_bytes()
    m=re.search(rb'(?ms)^'+str(n).encode()+rb' 0 obj.*?stream\r?\n(.*?)\r?\nendstream',b)
    v=zlib.decompress(m[1])
    print(name,n,hashlib.sha256(b).hexdigest(),hashlib.sha256(v).hexdigest())
    return v.decode('latin1')
pt=stream('PlattTrudgian1809.03134v2',80).splitlines()
assert '(4)-173.468(0)-2.83755(0)-2.83857(0)' in pt[346]
assert '(98)' not in pt[352] and '(3)-2.83857(5)-2.83857(6)' in pt[352] and '(3)-996.564(1)' in pt[358]
print('\n'.join(pt[344:365]))
rows=extract()
assert rows['PT1'][3]==(4000,'356.3','1.52','1.89','7.33e-16')
print('Extracted row counts', {k:len(v) for k,v in rows.items()})
def eis(v):
    t=sum(v**k/(k*factorial(k)) for k in range(1,181))
    return I('.57','.59')+log(v)+I(t,t+2*v**181/(181*factorial(181)))
v=log(2)
# Points of the interval v are positive and below one; evaluate endpoints for series.
li2=I(eis(F(v.l,1<<192)).l,eis(F(v.h,1<<192)).h,True)
ck(0,li2);ck(li2,2)
print('li_PV(2) in',li2.pt())
a=F('3.9')
ck(F('1.000000147')+F('1.78')*exp(-a/6),2)
ck(0,exp(-a)*eis(a)); ck(exp(-a)*eis(a),1)
d=((A,0,F(0)),(116,0,F(1,2)))
rhs=transfer(d,a,a,1+(A+116*exp(-a/2))/a)
ck(rhs,0)
print('Unguarded (6) counterexample RHS',rhs.pt())
u=F(61)
ck(u,exp(u/2)/6);ck(51,exp(u/2)/6);ck(exp(u/2)/6,(exp(u/2)-2)/5)
# These inequalities extend by monotonicity of exp(v/2)/v and exp(v/2).
hu=F(1000)
Rosser=lambda h:F('.137')*log(h)+F('.443')*log(log(h))+F('1.588')
ck(F('1e-12'),2*Rosser(H)/H)
ck(F('.99'),1-exp(-F(400)))
ck(F('1.04e-12'),PI/(T0-1))
ck(PI/(3*10**12),A)
assert all(coefficient(n)>0 for n in range(6,50))
# Ancillary slack for optional Dusart directional pi rows in the comparison.
v=F(170)
s2=1/v+1/v**2+2/v**3
assert v**4*(fu(v)-s2)<F('6.2')
w=F(1,170)
assert 1/(1-w-w*w)<1+w+2*w*w+4*w**3
# Last exact comparison is equivalent to 1-6w-4w^2>0,
# hence holds also for w in (0,1/170]. This covers both rational lower rows.
assert 1-6*w-4*w*w>0
assert F('.2311')*v-F('6.2')>1
assert F('.112')*v**2-2*v-F('6.2')>1
assert F('.53816')*v-F('6.2')>1
assert F('.2762')*v**2-2*v-F('6.2')>1
assert F('.2551')*v**3-v**2-2*v-F('6.2')>1
ck(F('.0039')*v**3*exp(-v/8),1)
# q(v)/v <= .0039 exp(-v/8)/v < 1/v^4 for v>=170.
for a,b,c in [(160,'.0263','.427'),(250,'.0182','.292'),(400,'.0151','.241')]:
    ck(F(c)*exp(-F(a,32)),F(b))
print('Optional original source comparisons, sign and endpoint arithmetic checked.')
