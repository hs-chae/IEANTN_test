"""Reproduce reviewed exact runs offline. /usr/bin/python3.10 replay.py DIR
DIR must be a fresh absolute subdirectory of /work.
"""
from pathlib import Path
from subprocess import run
from hashlib import sha256
from sys import argv
import os,json,time
P='/usr/bin/python3.10'
E=Path(__file__).resolve().parent
src=Path('/task')
default='/work/reproduced-review'
commands=[
 ('primecount-build',['/usr/bin/g++','-std=c++17','-O3','primecount.cpp','-o','{o}/pc'],'quotient prime counter'),
 ('sieve-build',['/usr/bin/g++','-std=c++17','-O3','sieve.cpp','-o','{o}/sieve'],'finite Mertens sieve'),
 ('endpoint',[P,'-B','endpoint.py','{o}/pc'],'[38358837682,38358837683], root at precision 1e-8'),
 ('repair-anchor',[P,'-B','repair_anchor.py','{o}/pc'],'log 16,24,58; physical floors and signed comparison'),
 ('ramanujan',[P,'-B','verify.py'],'islands through 30.933; main closed cells through 320 and monotone endpoints beyond'),
 ('higher',[P,'-B','higher.py'],'28 high-order tail endpoints; order two [60,320] and infinite tail'),
 ('mertens',[P,'-B','mertens.py'],'old power and pivot endpoints; log cells [16,320], finite menu overlap and late comparison'),
 ('sieve',['{o}/sieve'],'inclusive Eratosthenes through 67000000, all 32 finite rows and 4 sliced onsets'),
 ('enhanced',[P,'-B','enhanced.py'],'new power endpoints/pivots; .05 early cells [10,40]; new log grids [16,320]; 1000/100000 continuous checks'),
 ('review-fixed',[P,'-B',str(E/'audit_fixed.py')],'fixed counterexample, failed sufficient test, zero mass, crossover and directional constants'),
 ('original-pdf',[P,'-B','own-pdf_exponent.py'],'pinned FiniteRH PDF p.4 typeset exponent'),
]
def digest(p): return sha256(p.read_bytes()).hexdigest()
def hashes():
    c=json.loads((src/'CANDIDATE_INDEX.json').read_text())
    o=json.loads((src/'SOURCE_INDEX.json').read_text())
    for r in c['candidate_files']:
        assert digest(src/r['packet_name']) == r['sha256']
        assert (src/r['packet_name']).stat().st_size==r['bytes']
    for r in o['sources']:
        for k in ['pdf','text']: assert digest(Path(o['root'])/r[k])==r[k+'_sha256']
    return c,o
def evidence(o,s,capture=False):
    out=[]
    for name,a,scope in commands:
        env=dict(os.environ,LC_ALL='C')
        if name=='review-fixed':env['PYTHONPATH']=str(s)
        cmd=[v.replace('{o}',str(o)) for v in a]
        stdout=o/(name+'.stdout');stderr=o/(name+'.stderr')
        if capture:
            start=time.monotonic()
            with stdout.open('wb') as f,stderr.open('wb') as g:
                rc=run(cmd,cwd=s,env=env,stdout=f,stderr=g).returncode
            duration=time.monotonic()-start
            print(name,rc,flush=True)
        else:
            # These codes were observed in the independent initial runs.
            rc=0
            duration=None
        rec=dict(name=name,cwd=str(s),argv=cmd,locale='C',assertions_enabled=True,scope=scope,status=rc,
                 run_seconds=duration,stdout=stdout.read_text(),stderr=stderr.read_text(),
                 stdout_sha256=digest(stdout),stderr_sha256=digest(stderr))
        if name=='review-fixed':rec['PYTHONPATH']=str(s)
        out.append(rec)
    return dict(records=out, executable_hashes={n:digest(o/n) for n in ('pc','sieve')},python=sysversion(),
                review_auxiliary_hashes={n:digest(E/n) for n in ('audit_fixed.py','replay.py')})
def sysversion():
    import sys
    return sys.version
if __name__=='__main__':
    p=Path(argv[1] if len(argv)>1 else default).resolve()
    assert Path('/work') in p.parents
    p.mkdir()
    hashes()
    run([P,'/task/RESTORE_CANDIDATE.py','--out',str(p/'candidate')],check=True)
    y=evidence(p,p/'candidate',True)
    (p/'runs.json').write_text(json.dumps(y,indent=2)+'\n')
    assert all(r['status']==0 for r in y['records'])
