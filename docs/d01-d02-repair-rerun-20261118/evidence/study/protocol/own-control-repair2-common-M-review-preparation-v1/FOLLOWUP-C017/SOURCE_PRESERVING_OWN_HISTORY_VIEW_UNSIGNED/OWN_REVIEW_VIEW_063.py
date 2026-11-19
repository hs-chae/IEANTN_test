from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess,hashlib,json,time
root=Path('/work/c017')
out=Path(__file__).resolve().parent
jobs=[('source_audit.py',),('certify.py',),('endpoint.py',),('finite_mertens.py','25000000'),('finite_joins.py',),('finite_zoom.py',),('evaluate.py','log','200')]
def run(args):
 cmd=['/usr/bin/python3.10',*args]
 t=time.monotonic()
 p=subprocess.run(cmd,cwd=root,capture_output=True)
 f=out/('replay_'+args[0]+'.txt')
 f.write_bytes(p.stdout)
 s=out/('replay_'+args[0]+'.stderr')
 s.write_bytes(p.stderr)
 return dict(command=cmd,cwd=str(root),returncode=p.returncode,elapsed_seconds=round(time.monotonic()-t,3),stdout=f.name,stderr=s.name,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
(out/'replay_receipts.jsonl').write_text('')
with ThreadPoolExecutor(max_workers=4) as ex:
 for a in ex.map(run,jobs): 
  with (out/'replay_receipts.jsonl').open('a') as f: print(json.dumps(a),file=f)
