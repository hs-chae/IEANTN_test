import sys,os,json,subprocess,time,hashlib
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
D=Path('/data/ivy-rh-080-20261125');F=D/'network/Solutions/RH080Study.v1/ablation/followup';O=D/'followup-portable-review-allmode-v1';PY=Path('/data/ivy-rh-one-prime-20261124/analytic/arb-venv/bin/python');REF=D/'network/Solutions/RHOnePrimeEvolution.v1/analytic/external-certifiers-frozen-v1/certify_gaussian_objective.py'
def need(q,m):
 if not q:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
need(int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024>384*2**30,'RAM reserve')
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
jobs=[]
for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 for kind in ['explicit','trapezoid','gaussian']:
  if kind=='gaussian' and mode=='OO':continue
  out=O/(kind+'-'+mode)
  if kind=='explicit':args=['--submitted',str(F/'timely-prefixes/functional-L2_E2_D1_V0-r1/prefix-0003'),'--certificates',str(F/'independent-global-chord/inputs'),'--out',str(out)]
  elif kind=='trapezoid':args=['--submitted',str(F/'timely-prefixes/cube-L2_E2_D1_V1-r1/prefix-0002'),'--out',str(out)]
  else:args=['--audit',str(F/'evidence/FOLLOWUP_REAUDIT_normal.json'),'--reference',str(REF),'--python-flint',str(PY),'--curated-root',str(F/'timely-prefixes'),'--out',str(out)]
  controller=F/('verify_gaussian_artifacts.py' if kind=='gaussian' else 'verify_explicit_arithmetic.py' if kind=='explicit' else 'verify_trapezoid_arithmetic.py')
  jobs.append((mode,kind,controller,out,[str(PY),*flags,str(controller),*args]))
def one(row):
 mode,kind,controller,out,cmd=row;start=time.monotonic();before=sha(controller)
 with (O/(kind+'-'+mode+'.stdout')).open('wb') as a,(O/(kind+'-'+mode+'.stderr')).open('wb')as b:r=subprocess.run(cmd,env=env,stdout=a,stderr=b,timeout=300)
 need(r.returncode==0,kind+' '+mode+' rejected');need(sha(controller)==before,'source changed');j=json.loads((out/'RESULT.json').read_text())
 if kind=='gaussian':need(sum(x['status'].startswith('PASS_') for x in j['cases'])==8,'Gaussian targets')
 elif kind=='explicit':need(all(x['status'].startswith('PASS_') for c in j['cases'] for x in c['tests']),'explicit target')
 else:need(j['status'].startswith('PASS_SECOND_'),'trapezoid target')
 return dict(kind=kind,mode=mode,command=cmd,returncode=r.returncode,seconds=time.monotonic()-start,controller_sha256=before,result_sha256=sha(out/'RESULT.json'))
with ThreadPoolExecutor(max_workers=2)as p:rows=list(p.map(one,jobs))
# Preserve equivalent numerical comparisons, not timing/path-dependent byte equality.
negative=[]
for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 for kind in ['explicit','trapezoid','gaussian']:
  row=next(r for r in jobs if r[0]==mode and r[1]==kind) if not(kind=='gaussian' and mode=='OO') else next(r for r in jobs if r[1]=='gaussian')
  cmd=list(row[4]);cmd[1:1+len([])]=[]
  # Reconstruct mode flags explicitly, keeping all other accepted arguments.
  idx=cmd.index(str(row[2]));cmd=[str(PY),*flags,*cmd[idx:]]
  proc=subprocess.run(cmd,env=env,capture_output=True,timeout=10)
  need(proc.returncode!=0 and b'Fresh' in proc.stderr,'stale-output guard not effective')
  negative.append(dict(kind=kind,mode=mode,case='stale-output',returncode=proc.returncode))
 for kind,script in [('gaussian','verify_gaussian_artifacts.py'),('explicit','verify_explicit_arithmetic.py'),('trapezoid','verify_trapezoid_arithmetic.py')]:
  p=subprocess.run([str(PY),*flags,str(F/script),'--out'],env=env,capture_output=True,timeout=10);need(p.returncode==2,'CLI argument guard')
  negative.append(dict(kind=kind,mode=mode,case='missing-required-argument',returncode=p.returncode))
record=dict(status='PASS_PORTABLE_CURATED_INPUT_ALLMODE_REPLAYS_AND18_ACTUAL_CLI_GUARDS',positive_runs=rows,negative_cases=negative,OO_gaussian_already_accepted_result_sha256=sha(D/'followup-gaussian-curated-v2-OO/RESULT.json'),workers=2,source_math_changed=False,new_model_calls=0,scope='Bounded external arithmetic/controller reproduction only; no extra Lean closure or PV claim.')
(O/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n');print(record['status'],flush=True)
