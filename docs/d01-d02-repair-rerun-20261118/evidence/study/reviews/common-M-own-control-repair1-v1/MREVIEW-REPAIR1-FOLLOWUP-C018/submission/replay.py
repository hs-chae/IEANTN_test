#!/usr/bin/python3.10
import hashlib,json,sys,os,subprocess,time,concurrent.futures
from pathlib import Path
t=Path('/task'); p=Path('/work/c018'); s=Path('/work/submission'); s.mkdir(exist_ok=True)
P='/usr/bin/python3.10'
H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
if not p.exists(): subprocess.run([P,str(t/'RESTORE_CANDIDATE.py'),'--out',str(p)],check=True)
ci=json.loads((t/'CANDIDATE_INDEX.json').read_text())
si=json.loads((t/'SOURCE_INDEX.json').read_text())
for r in ci['candidate_files']: assert H(t/r['packet_name'])==H(p/r['original_name'])==r['sha256']
for r in si['sources']:
 for k in ['pdf','text']:assert H(Path(si['root'])/r[k])==r[k+'_sha256']
jobs=[('gcc',['/usr/bin/gcc','--version'],0),('python',[P,'-VV'],0),('endpoint',[P,'endpoint.py'],0),('audit',[P,'audit.py'],1),
('compile',['/usr/bin/gcc','-O3','-std=c11','finite.c','-o','/work/c018/review-finite'],0)]
for m in (0,1):
 for cmd in ['certify R','certify M','higher','ramref','refine','comparison','diagnostics']:
  f,*args=cmd.split(); jobs.append((cmd.replace(' ','-')+'-'+str(m),[P,f+'.py']+args,m))
def run(j):
 name,argv,m=j
 env={'LC_ALL':'C','RAM_ONLY':str(m),'PYTHONHASHSEED':'0'}; start=time.monotonic()
 with (s/(name+'.out')).open('wb') as o,(s/(name+'.err')).open('wb') as e:
  v=subprocess.run(argv,cwd=p,env=dict(os.environ,**env),stdout=o,stderr=e)
 return dict(name=name,argv=argv,cwd=str(p),env=env,status=v.returncode,seconds=time.monotonic()-start,stdout_sha256=H(s/(name+'.out')),stderr_sha256=H(s/(name+'.err')))
rec=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for r in pool.map(run,jobs):
  rec.append(r)
  (s/'receipts.json').write_text(json.dumps(rec,indent=2)+'\n')
rec += [run(('finite',['/work/c018/review-finite'],0))]
(s/'receipts.json').write_text(json.dumps(rec,indent=2)+'\n')
(s/'binary-sha256.txt').write_text(H(p/'review-finite')+'\n')
assert all(r['status']==(1 if r['name']=='audit' else 0) for r in rec)
for i in range(2):assert 'not certified' not in (s/f'ramref-{i}.out').read_text()
for a,b in [('endpoint','endpoint-evidence.txt'),('finite','finite-evidence.txt'),('ramref-1','refine-R-evidence.txt'),('refine-1','refine-M-evidence.txt')]:
 assert H(s/(a+'.out'))==H(p/b),(a,b)
