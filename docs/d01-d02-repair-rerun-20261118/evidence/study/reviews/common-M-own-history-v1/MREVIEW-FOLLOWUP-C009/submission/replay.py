"""Replay locked source. Run /usr/bin/python3.10 -B replay.py GROUP."""
import os,subprocess,json,hashlib,time,sys
from pathlib import Path
p=Path('/work/review-input')
o=Path('/work/submission')
py='/usr/bin/python3.10'
g='/usr/bin/g++'
def digest(raw):return hashlib.sha256(raw).hexdigest()
env=dict(os.environ,PATH='/usr/bin:/bin',LC_ALL='C',PYTHONDONTWRITEBYTECODE='1')
env.pop('PYTHONOPTIMIZE',None)
group=sys.argv[1]
r={}
def run(key,args,ref=None):
 t=time.monotonic()
 a=subprocess.run(args,cwd=p,env=env,capture_output=True)
 row=dict(command=args,cwd=str(p),status=a.returncode,elapsed=time.monotonic()-t,stdout=a.stdout.decode(),stderr=a.stderr.decode(),stdout_sha256=digest(a.stdout),stderr_sha256=digest(a.stderr))
 if ref: row.update(reference=ref,reference_sha256=digest((p/ref).read_bytes()),identical=a.stdout==(p/ref).read_bytes())
 r[key]=row
 (o/('evidence_'+group+'.json')).write_text(json.dumps(r,indent=2)+'\n')
 return a.returncode
for row in json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())['candidate_files']:
 assert digest((p/row['original_name']).read_bytes())==row['sha256']
if group=='new':
 for s in 'normalize_replay spectral refine2 higher2 compare2 order192 joins2 mid2 m2 extra2 lowpoly2'.split():
  refs={'refine2':'refine2.out','lowpoly2':'lowpoly2_analytic.out'}
  run(s,[py,'-B',s+'.py'],refs.get(s,s+'.out'))
if group=='old':
 for key,args,ref in [('endpoint',['cert.py','endpoint'],'endpoint.out'),('higher',['cert.py','tails'],'higher.out'),('mcert',['mcert.py'],'mertens_analytic.out'),('repair',['repair_cert.py'],'repair.out'),('repair_mpoly',['repair_mpoly.py'],'repair_mpoly_analytic.out'),('m_poly_2b',['m_poly_2b.py'],'m_poly_2b_analytic.out'),('ranu',['cert.py'],'ranu.out')]:
  run(key,[py,'-B']+args,ref)
if group.startswith('scan_'):
 s=group[5:]
 b='/work/check_'+s
 if run('build',[g,'-O3','-std=c++17',s+'.cc','-o',b])==0:
  run(s,[b],'lowpoly2_scan.out' if s=='lowpoly2' else s+'.out')
  r[s]['binary_sha256']=digest(Path(b).read_bytes())
  if s=='mertens':
   dest=Path('/work/c009_mertens_stdout')
   dest.write_text(r[s]['stdout'])
   run('witness',[py,'-B','witness.py',str(dest)],'witness.out')
  (o/('evidence_'+group+'.json')).write_text(json.dumps(r,indent=2)+'\n')
if group=='aux':
 run('restore',[py,'-B','/task/RESTORE_CANDIDATE.py','--out','/work/c009_restore_evidence'])
 run('compiler_version',[g,'--version'])
 run('python_version',[py,'--version'])
 run('aux',[py,'-B',str(o/'checks.py')])
 run('old_aux',[py,'-B','D01_M_REVIEW_ancillary.py','/work/c009_mertens_stdout'])
if group=='source':
 run('source_pdf',[py,'-B','D01_M_REVIEW_source_readback.py'],'D01_M_REVIEW_source_readback.out')
