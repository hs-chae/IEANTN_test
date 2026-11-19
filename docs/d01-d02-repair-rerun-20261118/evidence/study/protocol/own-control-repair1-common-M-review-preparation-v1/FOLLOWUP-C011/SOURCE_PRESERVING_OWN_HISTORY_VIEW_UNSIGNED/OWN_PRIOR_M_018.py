from pathlib import Path
import hashlib, subprocess, os, sys, json, time
p=Path(__file__).resolve().parent
r=Path(sys.argv[1])
py='/usr/bin/python3.10'
if not r.exists():
 subprocess.run([py,'/task/RESTORE_CANDIDATE.py','--out',str(r)],check=True)
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for row in idx['candidate_files']:
 assert hashlib.sha256((r/row['original_name']).read_bytes()).hexdigest()==row['sha256']
cmd=[py,sys.argv[2]]
t=time.monotonic()
s=subprocess.run(cmd,cwd=r,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True)
def read(b): return {'sha256':hashlib.sha256(b).hexdigest(),'text':b.decode()}
q={'argv':cmd,'cwd':str(r),'status':s.returncode,'seconds':time.monotonic()-t,'python':sys.version,'stdout':read(s.stdout),'stderr':read(s.stderr)}
if len(sys.argv)>3:
 b=(r/sys.argv[3]).read_bytes()
 q.update(candidate_output=sys.argv[3],candidate_output_sha256=hashlib.sha256(b).hexdigest(),stdout_exact_match=b==s.stdout)
(p/(sys.argv[2]+'.receipt.json')).write_text(json.dumps(q,indent=2))
print(sys.argv[2],s.returncode,q['seconds'],q.get('stdout_exact_match'),flush=True)
