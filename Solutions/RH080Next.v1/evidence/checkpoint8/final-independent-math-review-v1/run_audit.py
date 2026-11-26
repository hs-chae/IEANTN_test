import hashlib,json,os,subprocess,time
from pathlib import Path
D=Path('/data/ivy-rh080-next-20261125')
O=D/'final-independent-math-review-v1'
C=json.loads(Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text())
P=D/'fft-fap-main-batch-v2/PLAN.json'
plan=json.loads(P.read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
checks=[]
for r in plan['accepted_dependencies']:
 for path,expected,kind in [(r['source_origin'],r['source_sha256'],'source'),(r['object_origin'],r['object_sha256'],'object')]:
  actual=sha(path)
  if actual!=expected: raise SystemExit(f'FAIL {kind}: {path}')
  checks.append({'path':path,'sha256':actual,'kind':kind})
for r in plan['source_rows']:
 p=Path(r['origin']); obj=D/'fft-fap-main-batch-v2/objects'/Path(r['module'].replace('.','/')+'.olean')
 if sha(p)!=r['source_sha256']: raise SystemExit(f'FAIL current source: {p}')
 receipt=json.loads((D/'fft-fap-main-batch-v2'/(r['module']+'.COMPILED.json')).read_text())
 # Actual compile receipts associate source/object and can be inspected without trusting a completion message.
 checks.append({'path':str(p),'sha256':sha(p),'kind':'source','object':str(obj),'object_sha256':sha(obj),'receipt':receipt})
if sha(C['compiler'])!=C['compiler_sha256']: raise SystemExit('FAIL compiler pin')
(O/'ASSOCIATED_INPUTS.json').write_text(json.dumps({'plan':str(P),'plan_sha256':sha(P),'checks':checks},indent=2)+'\n')
env=dict(os.environ)
env['LEAN_PATH']=str(D/'fft-fap-main-batch-v2/objects')+':'+C['generic_lean_path']
cmd=[C['compiler'],'-o',str(O/'FinalMathAudit.olean'),str(O/'FinalMathAudit.lean')]
start=time.monotonic()
with (O/'audit.stdout').open('w') as out,(O/'audit.stderr').open('w') as err:
 result=subprocess.run(cmd,env=env,stdout=out,stderr=err,cwd=O)
if result.returncode!=0: raise SystemExit(f'FAIL Lean audit rc={result.returncode}')
if 'INDEPENDENT_FINAL_MATH_PASS' not in (O/'audit.stdout').read_text(): raise SystemExit('FAIL missing explicit audit gate')
for c in checks:
 if sha(c['path'])!=c['sha256']: raise SystemExit(f'FAIL changed input during audit: {c["path"]}')
receipt={'status':'PASS_ASSOCIATED_INDEPENDENT_TYPE_AND_PROOF_CONSUMPTION_AUDIT','source_cold':False,'fresh_Lean_audit_roots':1,'actual_final_theorems':9,'runtime_seconds':time.monotonic()-start,'command':cmd,'returncode':result.returncode,'compiler_sha256':C['compiler_sha256'],'audit_source_sha256':sha(O/'FinalMathAudit.lean'),'stdout_sha256':sha(O/'audit.stdout'),'stderr_sha256':sha(O/'audit.stderr'),'object_sha256':sha(O/'FinalMathAudit.olean'),'input_index_sha256':sha(O/'ASSOCIATED_INPUTS.json'),'W4_actual_norm_or_main_glues_accepted':False,'boundary':'Current mathematical chain through explicit W4 norm premise and actual finite Fap full-main consumers only. W4 N24/main completion remains separate.'}
(O/'LEAN_AUDIT_RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
