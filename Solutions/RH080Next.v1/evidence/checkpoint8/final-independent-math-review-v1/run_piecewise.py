import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--label',required=True,choices=['normal','-O','-OO']);a=p.parse_args()
O=Path('/data/ivy-rh080-next-20261125/final-independent-math-review-v1');R=O/('piecewise-v2-'+a.label)
R.mkdir(exist_ok=False)
C=json.loads(Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=O/'PiecewiseMathAuditV2.lean';frozen=sha(source)
if sha(C['compiler'])!=C['compiler_sha256']:raise SystemExit('FAIL compiler hash')
env=dict(os.environ);env['LEAN_PATH']='/data/ivy-rh080-next-20261125/fft-fap-main-batch-v2/objects:'+C['generic_lean_path']
cmd=['/usr/bin/time','-v',C['compiler'],'-o',str(R/'PiecewiseMathAuditV2.olean'),str(source)]
start=time.monotonic()
with (R/'stdout').open('w') as out,(R/'stderr').open('w') as err:r=subprocess.run(cmd,env=env,stdout=out,stderr=err,cwd=O)
if r.returncode!=0:raise SystemExit(f'FAIL compiler rc={r.returncode}')
s=(R/'stdout').read_text()
if 'INDEPENDENT_EXACT_PIECEWISE_STD3_PASS' not in s:raise SystemExit('FAIL explicit Lean axiom gate')
matched=re.findall(r"'IndependentFinalMathReview\.exact_piecewise_from_current_math' depends on axioms:\s*\[([^\]]*)\]",s)
if len(matched)!=1:raise SystemExit('FAIL strict axiom-list parse')
names=[x.strip() for x in matched[0].split(',')]
if len(names)!=3 or set(names)!={'propext','Classical.choice','Quot.sound'}:raise SystemExit('FAIL exact Std3 list')
if sha(source)!=frozen:raise SystemExit('FAIL source changed')
x={'status':'PASS_INDEPENDENT_FIVE_BRANCH_RECONSTRUCTION_WITH_EXPLICIT_W4_NORM','label':a.label,'command':cmd,'returncode':r.returncode,'runtime_seconds':time.monotonic()-start,'source_sha256':frozen,'stdout_sha256':sha(R/'stdout'),'stderr_sha256':sha(R/'stderr'),'object_sha256':sha(R/'PiecewiseMathAuditV2.olean'),'does_not_close_W4_norm':True,'axioms':names}
tmp=R/'RESULT.json.tmp';tmp.write_text(json.dumps(x,indent=2)+'\n');tmp.replace(R/'RESULT.json');print(json.dumps(x))
