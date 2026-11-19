"""Run the locked Python programs on unmodified restored bytes."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess, sys, json, hashlib, time, argparse
ap=argparse.ArgumentParser()
ap.add_argument('--candidate', default='/work/c017')
ap.add_argument('--jobs', type=int,default=4)
args=ap.parse_args()
C=Path(args.candidate)
S=Path(__file__).resolve().parent
if not C.exists():
    subprocess.run([sys.executable, '/task/RESTORE_CANDIDATE.py', '--out', str(C)],check=True)
index=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
for f in index['candidate_files']:
    assert hashlib.sha256((C/f['original_name']).read_bytes()).hexdigest()==f['sha256']
runs=[('source_audit',[]),('certify',[]),('endpoint',[]),('finite_mertens',[]),('finite_joins',[]),('finite_zoom',[]),('evaluate',['log','200']),('repair_finite',[]),('repair_spectral',[]),('repair_r',[]),('repair_joins',[]),('repair_portfolio',[]),('repair_evaluate',['log','200'])]
def run(el):
    f,args=el
    cmd=[sys.executable,'-B',f+'.py',*args]
    t=time.monotonic()
    p=subprocess.run(cmd,cwd=C,capture_output=True)
    rec={'command':cmd,'cwd':str(C),'status':p.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'stdout':p.stdout.decode(),'stderr':p.stderr.decode(),'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr).hexdigest()}
    (S/(f+'_receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(f,p.returncode,rec['elapsed_seconds'],flush=True)
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    list(pool.map(run,runs))
