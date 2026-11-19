#!/usr/bin/python3.10
# Ancillary checks only; same analytic/certificate algorithms, no parameter optimization.
import os, sys, json, hashlib, subprocess, re
from pathlib import Path
root=Path('/task'); exact=Path('/work/exact')
sys.path.insert(0,str(exact))
from cert import *
from mertens import pure
from runpy import run_path
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for row in json.loads((root/'SOURCE_INDEX.json').read_text())['sources']:
    for kind in ('pdf','text'):
        p=Path('/corpus/originals')/row[kind]
        assert sha(p)==row[kind+'_sha256']
        print('source',p,sha(p))
for row in json.loads((root/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
    p=exact/row['original_name']; assert sha(p)==sha(root/row['packet_name'])==row['sha256']
    print('candidate',p,sha(p))
for mode,L,target in [(0,Q('189.125'),[1,14,78]),(0,Q(172),[1,14,100]),(0,Q(724),[g(n) for n in range(4,27)])]:
    from cert import loss
    d=Hmain(L,27)-sum(I(c)/I(L)**j for j,c in enumerate(target))-loss(L,L,mode)
    print('B0 point certificate slack (not true gap)',L,d)
    assert d.b<0
for mode,a in [(0,Q(1,8)),(1,Q(5,32))]:
    cs=[x*200**2*(-I(a)*200).exp() for x in pure(Q(200),mode)]
    print('Mertens L=200 rescaled inverse-log actual interval certificate',mode,cs)
    assert max(x.b for x in cs)<D('.0223')
    vs=[x*(-I(a)*200).exp()/(200 if j<2 else 1) for j,x in enumerate(pure(Q(200),mode))]
    ups=[['1.305e-15','1.305e-15','2.610e-13'],['3.482e-17','3.482e-17','6.964e-15']][mode]
    assert all(x.b<D(z) for x,z in zip(vs,ups))
assert (I('.260')*200**2*(-I(Q(5,32))*200).exp()).b<D('.0223')
assert (I('.01880')*200**2*(-I(25)).exp()).b<D('.0223')
assert (I('.260')*(-I(Q(1,32))*200).exp()).b<D('.01')
assert (I(2)*(I(17).exp())/34).b<I(34).exp().a # coarser check supplemented below
assert (2*I('3.14159265358979323847')**2/34*(-I(17)).exp()).b<1
# In ramanujan.md:117 compare the normalized psi-only transport; max rate is <=1/2.
assert (I('.3')*(-I(Q(5,32))*200).exp()*(1+1/(I(200)*(Q(1,2)-Q(2,58))))).b<CH[0][0].a
# Verify candidate anchor's existing grid with one upward addition at line 26.
p=exact/'anchor.py'
orig=p.read_text()
old="br.a.copy_negate()+D('0.00000000025')"
assert orig.count(old)==1
ns={'__file__':str(p),'__name__':'review_anchor'}
exec(compile(orig.replace(old,"hi(lambda:br.a.copy_negate()+D('0.00000000025'))"),str(p),'exec'),ns)
print('anchor with line 26 pad rounded upward:')
ns['chk']()
for file in ['endpoint','early','mertens','anchor','cert']:
    p=Path(__file__).resolve().parent/(file+'.log')
    if not p.exists():continue
    m=dict(early='early',mertens='mertens',endpoint='endpoint',anchor='anchor',cert='ram')[file]
    status=p.read_bytes().splitlines(keepends=True)
    if status and b'_status=' in status[-1]:
        assert status[-1].endswith(b'=0\n')
        assert b''.join(status[:-1])==(exact/(m+'_receipt.txt')).read_bytes()
        print('byte-identical stdout',file,sha(p))
replay=Path('/work/sieve_replay.txt')
if replay.stat().st_size:
    assert replay.read_bytes()==(exact/'sieve_receipt.txt').read_bytes()
    print('byte-identical stdout sieve',sha(replay))
