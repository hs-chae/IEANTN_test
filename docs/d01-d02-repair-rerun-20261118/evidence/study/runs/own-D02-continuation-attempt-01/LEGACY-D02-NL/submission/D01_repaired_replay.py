"""Reproduce the submitted ordinary certificates. Writes only under /work.

Default: all exact historical and current checks. Optional 'new': only new
checks and the historical dependencies needed by those checks. No network.
"""
from pathlib import Path
import os, subprocess, tempfile, sys, hashlib, json

src=Path(__file__).resolve().parent
py='/usr/bin/python3.10'
gcc='/usr/bin/gcc'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
root=Path(tempfile.mkdtemp(prefix='portfolio-replay-',dir='/work'))
env['TMPDIR']=str(root)

def run(args,cwd,tag,stdin=None):
    target=root/(tag+'.out')
    with target.open('wb') as out:
        if stdin is None: subprocess.run(args,cwd=cwd,env=env,stdout=out,check=True)
        else:
            with stdin.open('rb') as f: subprocess.run(args,cwd=cwd,env=env,stdin=f,stdout=out,check=True)
    print(tag,hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
    return target

def rebuild(stage):
    d=root/stage
    d.mkdir()
    for f in src.glob(stage+'_*'):
        (d/f.name.split('_',1)[1]).write_bytes(f.read_bytes())
    return d

if __name__=='__main__':
    # The submitted lock covers both exact historical payloads and new files.
    lock=json.loads((src/'LOCK.json').read_text())
    assert set(lock)=={'files'}
    entries=lock['files']
    assert len({row['path'] for row in entries})==len(entries)
    for row in entries:
        assert set(row)=={'path','sha256'} and Path(row['path']).name==row['path']
        assert hashlib.sha256((src/row['path']).read_bytes()).hexdigest()==row['sha256']
    d1=rebuild('D01'); d2=rebuild('D02')
    run([py,'check.py'],d1,'d01-check')
    run([py,'pi_exact.py'],d1,'d01-pi')
    if sys.argv[1:]!=['new']:
        z1=root/'old-sieve'
        run([gcc,'-std=gnu11','-O3','-Wall','-Wextra','sieve.c','-o',z1],d1,'gcc-original')
        old=run([z1],d1,'d01-sieve')
        run([py,'endpoints.py'],d1,'d01-endpoints',old)
    for file in ['cert.py','density.py','mertens_tail.py','mertens_sieve.py','tertiary.py']:
        run([py,file],d2,'D02_'+file)
    z=root/'mertens-fixed'
    run([gcc,'-std=gnu11','-O3','-Wall','-Wextra','-fsanitize=undefined','-fno-sanitize-recover=undefined',
         'sieve_repaired.c','-o',z],src,'gcc-repaired')
    fresh=run([z],src,'repaired')
    run([py,'endpoints.py'],d1,'endpoints_repaired',fresh)
    run([py,'late.py'],src,'late')
    run([py,'power.py'],src,'power')
    run([py,'ram.py'],src,'ram-base')
    run([py,'ram.py','sensitivity'],src,'ram-sens')
    run([py,'mertens_new.py',fresh],src,'mertens-new')
    print('All requested replay steps passed. Logs:',root,flush=True)
