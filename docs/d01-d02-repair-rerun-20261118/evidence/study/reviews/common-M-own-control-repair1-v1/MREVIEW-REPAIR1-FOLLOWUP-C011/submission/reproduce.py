"""Reproduce reviewed certificate outputs without editing the locked /task packet.
Usage: /usr/bin/python3.10 reproduce.py /work/<fresh-restored-directory>
"""
import subprocess, os, json, hashlib, sys
from pathlib import Path
py='/usr/bin/python3.10'
r=Path(sys.argv[1]).resolve()
p=Path(__file__).resolve().parent
ix=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
by={z['original_name']:z['sha256'] for z in ix['candidate_files']}
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
subprocess.run([py,'/task/RESTORE_CANDIDATE.py','--out',str(r)],env=env,check=True)
def run(argv,cwd):
    proc=subprocess.run(argv,cwd=cwd,env=env,capture_output=True)
    print(json.dumps(dict(argv=argv,cwd=str(cwd),status=proc.returncode,
        stdout_sha256=hashlib.sha256(proc.stdout).hexdigest(),stdout=proc.stdout.decode(),
        stderr_sha256=hashlib.sha256(proc.stderr).hexdigest(),stderr=proc.stderr.decode())),
        flush=True)
    proc.check_returncode()
    return hashlib.sha256(proc.stdout).hexdigest()
for name in ('certificate','refine','checks','endpoint','small','source_rows','upgrade'):
    f=name+('.json' if name=='source_rows' else '.log')
    assert run([py,name+'.py'],r)==by[f]
run([py,'OWN_PRIOR_M_014.py'],r)
run([py,'ancillary.py',str(r)],p)
