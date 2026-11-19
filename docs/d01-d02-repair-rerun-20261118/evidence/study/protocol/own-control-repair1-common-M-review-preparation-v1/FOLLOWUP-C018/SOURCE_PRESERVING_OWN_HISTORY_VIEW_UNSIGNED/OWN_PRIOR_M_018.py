from pathlib import Path
import subprocess as s, os, hashlib as h, json, sys
base=Path('/work/review-c018'); out=Path('/work/submission')
py='/usr/bin/python3.10'
if not base.exists(): s.run([py,'/task/RESTORE_CANDIDATE.py','--out',str(base)],check=True)
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for r in idx['candidate_files']:assert h.sha256((base/r['original_name']).read_bytes()).hexdigest()==r['sha256']
jobs=[('R',[py,'certify.py','R']),('M',[py,'certify.py','M']),('high',[py,'higher.py']),('endpoint',[py,'endpoint.py']),('comparison',[py,'comparison.py']),('diag',[py,'diagnostics.py']),('build',['/usr/bin/gcc','-O3','-std=c11','finite.c','-o',str(base/'finite')]),('finite',[str(base/'finite')]),('gcc',['/usr/bin/gcc','--version']),('python',[py,'--version'])]
jobs += [(name+'-ram',argv) for name,argv in jobs if name in ('R','M','high','comparison')]
import concurrent.futures as cf
def run(j):
 name,args=j
 e=dict(os.environ,RAM_ONLY='1' if name.endswith('-ram') else '0')
 q=s.run(args,cwd=base,env=e,capture_output=True)
 obj=dict(argv=args,cwd=str(base),RAM_ONLY=e['RAM_ONLY'],status=q.returncode,stdout=q.stdout.decode(),stderr=q.stderr.decode(),stdout_sha256=h.sha256(q.stdout).hexdigest(),stderr_sha256=h.sha256(q.stderr).hexdigest())
 if name=='build' and not q.returncode:obj['binary_sha256']=h.sha256((base/'finite').read_bytes()).hexdigest()
 (out/('replay-'+name+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
 return name,q.returncode
with cf.ThreadPoolExecutor(4) as pool:
 tasks=[pool.submit(run,j) for j in jobs if j[0] not in ('finite','build')]
 if run(jobs[6])[1]==0:tasks.append(pool.submit(run,jobs[7]))
 for f in cf.as_completed(tasks):print(f.result(),flush=True)

name='ancillary'
q=s.run([py,str(out/'ancillary.py')],cwd=base,env=dict(os.environ,RAM_ONLY='1'),capture_output=True)
(out/('replay-'+name+'.json')).write_text(json.dumps(dict(argv=q.args,cwd=str(base),RAM_ONLY='1',status=q.returncode,stdout=q.stdout.decode(),stderr=q.stderr.decode(),stdout_sha256=h.sha256(q.stdout).hexdigest(),stderr_sha256=h.sha256(q.stderr).hexdigest()),indent=2)+'\n')
assert q.returncode==0,q.stderr
