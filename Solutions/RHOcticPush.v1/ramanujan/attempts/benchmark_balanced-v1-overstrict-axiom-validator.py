#!/usr/bin/env python3
"""Read-only numerical checker performance probe, not source-first PV.
The exact pre-existing Check0205 goal is kept; only proof evaluation is balanced.
Its huge source data belong to a separate, still-running historical study.
This script never modifies or interrupts that study.
"""
import argparse,hashlib,json,os,resource,signal,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
SOURCE="""import RamanujanPV.HighTransitionCount.Data
import BalancedCountCheck
namespace RHPushCountBalancedProbe
open RamanujanPV.QuotientDemandCheck RamanujanPV.HighTransitionCount
open RHOcticPush.BalancedCount
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem numeric : tree (checkEntry nodes gaps gapCount) 6717440 15=true := by decide +kernel
theorem exact_original : allFrom (checkEntry nodes gaps gapCount) 6717440 32768=true :=
  source_32768 numeric
#print axioms numeric
#print axioms exact_original
end RHPushCountBalancedProbe
"""
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--model-bank',type=Path,required=True)
    p.add_argument('--old-bank',type=Path,required=True)
    p.add_argument('--seconds',type=int,default=300)
    a=p.parse_args()
    need(not a.out.exists(),'Fresh output required')
    need(a.seconds>0,'Positive timeout required')
    need(a.old_bank.joinpath('RamanujanPV/HighTransitionCount/Data.olean').is_file(),'Original Data object missing')
    need(a.model_bank.joinpath('BalancedCountCheck.olean').is_file(),'Proved model missing')
    ctx=json.loads((ROOT/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text())
    need(sha(Path(ctx['compiler']))==ctx['compiler_sha256'],'Compiler mismatch')
    a.out.mkdir(parents=True)
    source=a.out/'CountBalancedProbe.lean';source.write_text(SOURCE)
    (HERE/'benchmarks/CountBalancedProbe.lean.txt').write_text(SOURCE)
    env=os.environ.copy()
    env['LEAN_PATH']=':'.join([str(a.model_bank),str(a.old_bank),*ctx['generic_libraries']])
    cmd=['taskset','-c','95','/usr/bin/time','-v','-o',str(a.out/'resources.txt'),ctx['compiler'],
         '--root='+str(a.out),'-j1',str(source),'-o',str(a.out/'CountBalancedProbe.olean')]
    def limit():resource.setrlimit(resource.RLIMIT_AS,(128<<30,128<<30))
    start=time.monotonic()
    with (a.out/'stdout').open('w') as out,(a.out/'stderr').open('w') as err:
        job=subprocess.Popen(cmd,env=env,stdout=out,stderr=err,preexec_fn=limit,start_new_session=True)
        timed=False
        try:code=job.wait(timeout=a.seconds)
        except subprocess.TimeoutExpired:
            timed=True;os.killpg(job.pid,signal.SIGTERM)
            try:code=job.wait(timeout=10)
            except subprocess.TimeoutExpired:os.killpg(job.pid,signal.SIGKILL);code=job.wait()
    result=dict(status='BOUNDED_TIMEOUT_NO_ACCEPTANCE' if timed else 'PASS' if code==0 else 'FAIL',
                elapsed=time.monotonic()-start,returncode=code,command=cmd,LEAN_PATH=env['LEAN_PATH'],
                source_sha256=sha(source),compiler_sha256=ctx['compiler_sha256'],
                old_data_object_sha256=sha(a.old_bank/'RamanujanPV/HighTransitionCount/Data.olean'),
                scope='Exact same original32768-record predicate, no numerical records/algorithm changed; '
                      'ordinary kernel certificate checking, no complete finite-count or PV claim',
                old_workers_unchanged=True,per_run_limit_GiB=128,
                stdout_sha256=sha(a.out/'stdout'),stderr_sha256=sha(a.out/'stderr'))
    if code==0:
        text=(a.out/'stdout').read_text()
        need("'RHPushCountBalancedProbe.numeric' does not depend on any axioms" in text,'Missing pure numerical leaf')
        need("'RHPushCountBalancedProbe.exact_original' depends on axioms: [propext]" in text,'Unexpected consumer axioms')
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'COUNT_BALANCED_PROBE.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__=='__main__':main()
