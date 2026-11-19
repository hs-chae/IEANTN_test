"""Reproduce exact candidate replay and archive stdout, stderr, status and hashes.
Use /usr/bin/python3.10 reproduce.py [fresh directory under /work].
File inputs come exclusively from the sealed packet and supplied original corpus.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys
p=Path('/task')
here=Path(__file__).resolve().parent
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/work/review-rerun')
assert root.parent==Path('/work') and not root.exists()
root.mkdir()
exe='/usr/bin/python3.10'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
hashbytes=lambda x:hashlib.sha256(x).hexdigest()
def run(args,tag):
    proc=subprocess.run(args,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    (root/(tag+'.stdout')).write_bytes(proc.stdout)
    (root/(tag+'.stderr')).write_bytes(proc.stderr)
    (root/(tag+'.status')).write_text(str(proc.returncode)+'\n')
    print(tag,proc.returncode,hashbytes(proc.stdout),hashbytes(proc.stderr),flush=True)
    proc.check_returncode()
    return proc.stdout.decode()
j=json.loads((p/'CANDIDATE_INDEX.json').read_text())
for s in json.loads((p/'SOURCE_INDEX.json').read_text())['sources']:
    for k in ['pdf','text']:
        assert hashbytes((Path('/corpus/originals')/s[k]).read_bytes())==s[k+'_sha256']
exact=root/'exact'
run([exe,str(p/'RESTORE_CANDIDATE.py'),'--out',str(exact)],'restore')
(exact/'LOCK.json').write_text(json.dumps({'files':[{'path':s['original_name'],'sha256':s['sha256']} for s in j['candidate_files']]}))
out=run([exe,str(exact/'replay.py')],'replay')
receipt={}
for line in out.splitlines():
    a=line.split()
    if len(a)==2:
        tag,digest=a; receipt[tag]=digest
d=Path(out.split('Logs: ')[1].strip())
for tag,digest in receipt.items():
    assert hashbytes((d/(tag+'.out')).read_bytes())==digest
run([exe,str(here/'audit_scalars.py'),str(exact)],'audit')
print('Proof-bearing source bytes and per-step replay stdout hashes checked.',root)
