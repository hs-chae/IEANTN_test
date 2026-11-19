"""Verify source identity, exact endpoint counterexample and decimal-vs-dyadic conversion.
Usage: /usr/bin/python3.10 audit.py EXACT_DIRECTORY [decimal]
The optional decimal mode observes exact accumulator values in the locked sieve;
the loop, algorithm, and parameters are unchanged.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import sys, json
p=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(p))
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for r in idx['candidate_files']:
    assert sha256((p/r['original_name']).read_bytes()).hexdigest()==r['sha256']
sources=json.loads((p/'SOURCE_INDEX.json').read_text())['sources']
for s in sources:
    for k in ['pdf','text']:
        assert sha256(Path('/corpus/originals',s[k]).read_bytes()).hexdigest()==s[k+'_sha256']
from D01_check import I, exp, log, less, PI, approx
from D02_cert import expi, WA, WA1, A0
n=38358837682
for x,a,b in [(F(n)+F('.1'),-7974586,-7974585),
              (F(n)+F('.217926'),-25,-24),
              (F(n)+F('.217927'),42,43)]:
    y=I(x)/exp(1)
    assert y.a//I(1).a==y.b//I(1).a==14111427770
    r=exp(1)*x*632207037/log(x)-1644673232**2
    less(a,r); less(r,b)
    print(x,a,b)
less(1/(8*PI),'.04')
less(log(I(3000175332800)/(2*PI))**2/I('6.28')+I('1.8642'),'117.02')
# For old D02 density switches use a piecewise logarithmic derivative,
# not the coarser global rate at s=20.
assert 1-F(2,20)>F(3,4)
assert 1-F(5,32)-F(2,169)>F(3,4)
assert 1-F(1,8)-F(2,187)>F(3,4)
# Check the already chosen optional historical switch with all its theta cost.
v=F('205.6')
assert WA(v)*expi(-5*v/32)[1]+4*expi(-v/2)[1]<F('1.048e-12')
assert F('117.5')+F('1.4262')-F('115.1')<4
assert WA(v)/50>WA1(v) and WA1(v)/50>2*A0
assert 2*F(1,2)**49*10**60 < __import__('math').factorial(49)
assert 2*F(1,3)**161*10**60 < 161*(1-F(1,9))
print('source identities, endpoint signs, elementary tails, plateau guards checked',flush=True)
if sys.argv[2:]==['local']:
    from gap_d02 import Model, Q, J, rad, carry, point, ram
    from mertens_d02 import constants, smooth_norm, rel
    from math import isqrt
    M=Model(14,24)
    for t,b,c in [('185.25',J,145),('215.5',Q,145)]:
        g=M.gap(I(t),b,6)
        less(g,c)
        print('method residual (not actual R)',t,b,approx(g),c)
    v=rel(smooth_norm(I('169.65'),J,'166.41','1.05e-12'),I('166.41'),J)
    less('.2569',v)
    print('failed wider smooth-envelope trial (not actual Mertens error)',approx(v))
    _,_,B3=constants()
    u=sum((log(p)/p for p in range(2,284)
           if all(p%d for d in range(2,isqrt(p)+1))),I(0))
    t=log(283)
    g=(u+B3-t)*exp(F(5,32)*t)
    less('.2707',g)
    print('actual normalized weighted deviation at x=283',approx(g))
if sys.argv[2:]==['decimal']:
    sys.modules['cert']=__import__('D02_cert')
    f=p/'D02_mertens_sieve.py'
    old=f.read_text()
    target="    print('finite Mertens certificate passed'"
    i=old.index(target)
    observer="""    observed=((gl-(qv+qd-sv)-Mth,gh-(qv-(sv+sd))-Mtl),
              (gl+vv+Vtl,gh+vv+vd+Vth))
    for (l,h),c,d in zip(observed,('.261497212838','1.332582275723'),
                         ('.261497212858','1.332582275744')):
        print('exact observed enclosure',l,h,S,flush=True)
        assert F(c)<=F(l,S)<=F(h,S)<=F(d)
"""
    exec(compile(old[:i]+observer+old[i:],str(f),'exec'),{'__name__':'__main__'})
