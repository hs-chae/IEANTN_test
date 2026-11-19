#!/usr/bin/python3.10
from pathlib import Path
import subprocess as sp, json, hashlib, os, sys, time, platform, decimal
task=Path('/task')
sub=Path(__file__).resolve().parent
work=Path('/work/exact-review')
sha=lambda b: hashlib.sha256(b).hexdigest()
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LC_ALL='C')
py='/usr/bin/python3.10'
g='/usr/bin/g++'
rec=[]
def run(cmd, match=None, label=None):
 t=time.monotonic()
 p=sp.run(cmd,cwd=work if work.exists() else '/work',env=env,capture_output=True)
 row=dict(cmd=cmd, cwd=str(work if work.exists() else '/work'), elapsed_s=round(time.monotonic()-t,3),status=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),stdout_sha256=sha(p.stdout),stderr_sha256=sha(p.stderr))
 if match:
  b=(work/match).read_bytes()
  row.update(expected=match,expected_sha256=sha(b),byte_equal=b==p.stdout)
 rec.append(row)
 print(label or cmd[-1],row['status'],row.get('byte_equal',''),row['elapsed_s'],flush=True)
 (sub/('replay_'+sys.argv[1]+'.json')).write_text(json.dumps(dict(python=sys.version,libmpdec=decimal.__libmpdec_version__,environment_overrides={"PYTHONDONTWRITEBYTECODE":"1","LC_ALL":"C"},runs=rec),indent=2)+'\n')
 return p
def build(src,out):
 p=run([g,'-O3','-Wall','-Wextra','-std=c++17',src,'-o',out])
 if p.returncode==0:
  rec.append(dict(binary=out,sha256=sha(Path(out).read_bytes())))
 return not p.returncode
if not work.exists(): run([py,str(task/'RESTORE_CANDIDATE.py'),'--out',str(work)])
run([g,'--version'])
for r in json.loads((task/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
 assert sha((work/r['original_name']).read_bytes())==r['sha256']
for r in json.loads((task/'SOURCE_INDEX.json').read_text())['sources']:
 for k in ['pdf','text']:
  assert sha((Path('/corpus/originals')/r[k]).read_bytes())==r[k+'_sha256']
if sys.argv[1]=='arithmetic':
 for s in ['mertens','sieve14','sieve_opt']:
  src='mertens.cpp'
  if s!='mertens':
   if run([py,s+'.py']).returncode: continue
   src='/work/'+s+'.cpp'
   rec.append(dict(generated=src,sha256=sha(Path(src).read_bytes())))
  if build(src,'/work/reviewer_'+s):run(['/work/reviewer_'+s], 'sieve_receipt.txt' if s=='mertens' else s+'_receipt.txt')
 if build('repair_m.cpp','/work/repair_m'):
  run([py,'repair_m.py'],'repair_m_receipt.txt')
elif sys.argv[1]=='analytic':
 if build('pcount.cpp','/work/pcount'):run([py,'endpoint.py'],'endpoint_receipt.txt')
 for name,r in [('ram_early','early'),('cert','ram'),('mertens','mertens'),('anchor','anchor'),('bridge14','bridge14'),('bridge_opt','bridge_opt'),('repair_ram','repair_ram'),('fixed49','fixed49'),('m_tail_extra','m_tail_extra')]:
  run([py,name+'.py'],r+'_receipt.txt')
 run([py,'cert.py','--high'],'high_receipt.txt')
elif sys.argv[1]=='failed_tests':
 run([py,'-c','from cert import main_ode; main_ode(28)'],label='historical order-28 start at 34')
 run([py,'-c','from cert import main_ode; main_ode(27,35)'],label='historical order-27 start at 35')
 run([py,'fixed49.py','0','7.7'],label='B0 coefficient 7.7 sufficient test')
elif sys.argv[1]=='order28':
 run([py,'-c','import cert; from repair_ram import wide_Finit; cert.Finit=wide_Finit; cert.main_ode(28,34)'],label='order-28 initial P test')
 run([py,'-c','import cert; from repair_ram import wide_Finit; cert.Finit=wide_Finit; cert.main_ode(28,35)'],label='order-28 initial C test')
elif sys.argv[1]=='printed_block':
 run([py,'-c','from cert import *; l,u=Q(484079,2560),Q(968163,5120); c=Q(77,10); slack=I(145-c)/I(u)**2+sum(I(g(k))/I(u)**(k-4) for k in range(7,28))-loss(l,u,0,False); print(l,u,slack); assert slack.b<0'])
elif sys.argv[1]=='historical_readback':
 src=work/'OWN_PRIOR_M_010.cpp'
 name=Path('/work/reviewer_historical_readback.cpp')
 name.write_bytes(src.read_bytes().replace(b'"/work/exact/mertens.cpp"',b'"/work/exact-review/mertens.cpp"'))
 rec.append(dict(generated=str(name),sha256=sha(name.read_bytes()),original=src.name,original_sha256=sha(src.read_bytes()),only_change='absolute include path to exact restored source'))
 if build(str(name),'/work/reviewer_historical_readback'):
  p=run(['/work/reviewer_historical_readback'])
  old=(work/'OWN_PRIOR_M_011.log').read_bytes().splitlines()
  assert p.stdout.splitlines()==[l for l in old if l.startswith((b'x*1000=',b'padded test:'))]
