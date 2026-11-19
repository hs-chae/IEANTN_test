#!/usr/bin/python3.10
"""Run exact packet source in a fresh /work directory, preserving separate stdout/stderr."""
from pathlib import Path
import hashlib, json, os, subprocess, sys, time
here=Path(__file__).resolve().parent
py='/usr/bin/python3.10'
jobs=[
 ('root-gap',['verify.py','root','gap'],'gap-replay.txt'),
 ('trade',['verify.py','trade'],'trade-replay.txt'),
 ('inherited-m',['mcheck.py'],'mcheck-replay.txt'),
 ('inherited-orders',['orders.py','0','6','12','19','25','50'],'orders-replay.txt'),
 ('new-r',['claims.py','early','rays','orders'],'claims-replay.txt'),
 ('localgap',['localgap.py'],'localgap-replay.txt'),
 ('new-m',['mnew.py'],'mnew-replay.txt'),
 ('small-finite',['mfinite.py'],'mfinite-replay.txt'),
 ('comparisons',['comparison.py'],'comparison-replay.txt'),
 ('ancillary',['-c','exec(compile(open('+repr(str(here/'ancillary.py'))+').read(), "ancillary.py", "exec"))'],None)]
assert len(sys.argv)==2, 'Use a fresh /work subtree: /usr/bin/python3.10 reproduce.py /work/replay-NEW'
out=Path(sys.argv[1]).resolve()
assert out.is_relative_to('/work') and not out.exists()
out.mkdir()
env={**os.environ,'LC_ALL':'C'}
cmd=[py,'/task/RESTORE_CANDIDATE.py','--out',str(out/'exact')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
recs={}
def run(name,args,inp=None):
 so=out/(name+'.stdout'); se=out/(name+'.stderr')
 start=time.monotonic()
 with so.open('wb') as h,se.open('wb') as e:
  p=subprocess.run(args,cwd=out/'exact' if (out/'exact').exists() else out,env=env,stdout=h,stderr=e,input=None if inp is None else inp.read_bytes())
 recs[name]=dict(argv=args,exit=p.returncode,elapsed_seconds=time.monotonic()-start,stdout=so.name,stderr=se.name,sha_stdout=sha(so),sha_stderr=sha(se),input=inp.name if inp else None)
 (out/'receipts.json').write_text(json.dumps(recs,indent=2)+'\n')
 assert p.returncode==0
 return so
run('restore',cmd)
def compare(actual,expected):
 s=actual.read_bytes()
 assert not any(bad in s for bad in (b'FAILED candidate',b'unverified',b'Traceback'))
 assert s==(out/'exact'/expected).read_bytes(),(actual.name,expected)
for name,args,ref in jobs:
 actual=run(name,[py,'-B','-u']+args)
 if ref:compare(actual,ref)
 else:assert actual.read_text()==(here/'ancillary.log').read_text().removesuffix('exit=0\n')
table=run('tables',[py,'-B','tables.py'])
bin=out/'primes-cert'
run('compile',['/usr/bin/g++','-O3','-std=c++17','-Wall','-Wextra','sieve.cpp','-o',str(bin)])
so=run('sieve',[str(bin)],table)
compare(so,'sieve-results.txt')
assert so.read_bytes()==(here/'sieve-run.stdout').read_bytes()
print('All reproduction comparisons passed.')

