"""Reproduce ordinary certificate evidence in a fresh /work directory.
Run with the assigned /usr/bin/python3.10 (no -O).
This invokes only locked candidate code and review ancillary checks.
"""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
py='/usr/bin/python3.10'
root=Path(tempfile.mkdtemp(prefix='independent-review-',dir='/work'))
exact=root/'exact'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
def run(argv,cwd,tag):
    r=subprocess.run([str(v) for v in argv],cwd=cwd,env=env,
                     capture_output=True)
    for suffix,raw in [('out',r.stdout),('err',r.stderr),
                      ('status',f'{r.returncode}\n'.encode())]:
        (root/(tag+'.'+suffix)).write_bytes(raw)
        print(tag,suffix,hashlib.sha256(raw).hexdigest(),flush=True)
    r.check_returncode()
run([py,'/task/RESTORE_CANDIDATE.py','--out',exact],root,'restore')
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
(exact/'LOCK.json').write_text(json.dumps({'files':[
    {'path':i['original_name'],'sha256':i['sha256']}
    for i in idx['candidate_files']]}))
run([py,'reproduce_d02.py','inheritance'],exact,'newreplay')
for mode in ('local','decimal'):
    run([py,Path(__file__).parent/'audit.py',exact,mode],exact,
        'dec' if mode=='decimal' else mode)
print('Saved replay evidence:',root)
