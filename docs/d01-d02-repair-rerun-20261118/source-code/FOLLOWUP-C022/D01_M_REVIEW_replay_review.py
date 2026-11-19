"""Reproduce review computations. Run /usr/bin/python3.10 -B replay_review.py.
Creates a fresh /work replay directory and stores stdout/stderr and statuses there.
Uses only the locked packet and this review's elementary ancillary verifier.
"""
from pathlib import Path
import os, sys, json, hashlib, tempfile, subprocess
P=Path('/task')
D=Path(__file__).resolve().parent
root=Path(tempfile.mkdtemp(prefix='c019-replay-',dir='/work'))
src=root/'candidate'; src.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for r in json.loads((P/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
    a=P/r['packet_name']; b=src/r['original_name']
    assert sha(a)==r['sha256']; b.write_bytes(a.read_bytes())
for r in json.loads((P/'SOURCE_INDEX.json').read_text())['sources']:
    for k in ('pdf','text'):
        assert sha(Path('/corpus/originals')/r[k])==r[k+'_sha256']
env=dict(os.environ,PYTHONPATH=str(src),REVIEW_EVIDENCE_DIR=str(root))
pyt=['/usr/bin/python3.10','-B']
def run(k,cmd):
    with (root/(k+'.stdout')).open('wb') as o,(root/(k+'.stderr')).open('wb') as e:
        r=subprocess.run(cmd,cwd=src,stdout=o,stderr=e,env=env)
    print(k,cmd,r.returncode,flush=True)
    assert r.returncode==0
g=['/usr/bin/g++','-O3','-std=c++17']
ex=str(root/'finite_opt')
run('compile',[*g,'finite_opt.cpp','-o',ex])
for k,args in [('finite100m',['100000000','1000000']),('finite20b',['20000000000','200000']),('finite26',[])]:
    run(k,[ex,*args])
    assert sha(root/(k+'.stdout'))==sha(src/(k+'.txt'))
ex=str(root/'finite24')
run('exact24_compile',[*g,'D01__SUBMITTED_007.cpp','-o',ex])
run('exact24',[ex])
assert sha(root/'exact24.stdout')==sha(src/'D01__SUBMITTED_008.txt')
for k,args,cmp in [('port',['portfolio_check.py'],'ram_replay'),
                   ('portDus',['portfolio_check.py','--dusart-only'],'ram_dusart_replay'),
                   ('portPrefix',['portfolio_check.py','--qrh-free-prefix'],'prefix_replay'),
                   ('M',['mertens_new.py'],'mertens_replay'),
                   ('MDus',['mertens_new.py','--dusart-only'],'mertens_dusart_replay'),
                   ('audit',['audit_summaries.py'],'summary_replay'),
                   ('Msieve',['mertens_check.py'],'mertens_results'),
                   ('secondary',['secondary_check.py'],None),
                   ('older_count',['count.py'],None),
                   ('ancillary_old',['-c','from refine import *; test_W2(); test_M(); test_short(); test_density();test_mertens()'],None),
                   ('ancillary',[str(D/'ancillary_verify.py')],None)]:
    run(k,pyt+args)
    if cmp: assert sha(root/(k+'.stdout'))==sha(src/(cmp+'.txt'))
print(root)
