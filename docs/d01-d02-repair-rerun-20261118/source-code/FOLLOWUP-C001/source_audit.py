"""Pinned source / retired branch audit and specific residual proof obstacles."""
from pathlib import Path
from hashlib import sha256
import json,zlib
from check import I,D,pi,Ch,grid,hp
from repair_check import C20,N20,loss,calibrate,poly
idx=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
root=Path(idx['root'])
for r in idx['sources']:
    for k in ['pdf','text']:
        p=root/r[k]
        assert sha256(p.read_bytes()).hexdigest()==r[k+'_sha256']
print('All seven PDF/extraction pairs match SOURCE_INDEX')
# Direct readback of the original pinned /Contents stream on PDF p.4.
p=(root/'PlattTrudgianFiniteRH.pdf').read_bytes()
s=p.split(b'\n114 0 obj\n',1)[1].split(b'stream\n',1)[1]
s=zlib.decompress(s).decode('latin1').split('\n')
print('FiniteRH PDF p.4, stream 114, lines 417-424:')
for j in range(416,424):print(j+1,repr(s[j]))
worst=D(0);n=0
for X,_ in grid('34','58','.025'):
    err=(Ch(X)+I('1.2551')*((-X/2).exp()+2*X*(-2*X/3).exp()))/X
    err+=I('.376')*(-X/2).exp()/X**2+I('12e-12')*(-X/8).exp()/X**2+10000*(-X).exp()
    ref=X*(-X/2).exp()/(8*pi)
    assert err.b<ref.a
    worst=max(worst,(err/ref).b);n+=1
print('Deleted branch is redundant on closed cells:',n,'ratio upper:',worst)
l=I(2).ln()
assert sum(c/a*(16*a).exp()*(1+2/l)/l**2 for c,a in [(I('.094'),I('.5')),(I('3e-12'),I('.875'))]).b<5000
assert (2*(1/l+1/l**2)+4/l**2+5).b<100
for k,c,p in [(376,I('.014'),2),(500,I('.005001'),4)]:
    L=I(k)
    assert (c*L**p*(-L/8).exp()).b<D('.040')
for k,m,mode in [(160,2,'density'),(210,1,'basic')]:
    L=I(k)
    r=hp(L,C20[5+m:])-L**(m+1)*loss(L,D(k),mode,N20)
    assert r.b<0
    print('Sufficient analytic surplus negative:',mode,k,m,r)
try:
    calibrate(32,poly(20,3)[0])
except AssertionError:
    print('Test of old anchor 32 with degree 20 and K=3 fails as stated')
else:
    raise AssertionError('expected rejected calibration')

