#!/usr/bin/env python3
"""Actual relocated-source replays; no application object fallback."""
import concurrent.futures,hashlib,json,os,subprocess,time
from pathlib import Path
B=Path(__file__).resolve().parent
R=B/'extracted';S=R/'Solutions/RH080Study.v1';Q=B/'proof-replay'
C=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json')
PY='/usr/bin/python3'
def need(v,m):
    if not v:raise ValueError(m)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
    t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def main():
    need((B/'RESULT.json').is_file(),'Archive/49restoration prerequisite missing')
    need(not Q.exists(),'Fresh replay storage required');Q.mkdir()
    available={x.split(':')[0]:int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith(('MemAvailable:','MemTotal:'))}
    need(available['MemAvailable']>=1024*2**30,'Recheck policy: 1TiB genuine available RAM required for this simultaneous replay plan')
    affinity=sorted(os.sched_getaffinity(0));need(len(affinity)>=20,'At least20 assigned hostCPUcores required')
    jobs=[]
    for i,lane in enumerate(['pv','g80','g56','estimates']):
        argv=[PY,S/'reproduce_study.py','--repository',R,'--context',C,'--run',Q/lane,'--lane',lane]
        jobs.append((lane,argv,affinity[4*i:4*i+4]))
    late=[('early369',[PY,S/'estimates/early369/reproduce.py','--repository',R,'--context',C,'--run',Q/'early369']),
          ('finite',[PY,S/'finite_frontier/reproduce.py','--root',R,'--context',C,'--run',Q/'finite']),
          ('competition',[PY,S/'reports/reproduce_competition_scalar.py','--context',C,'--run',Q/'competition'])]
    save(Q/'PLAN.json',dict(status='EXTRACTED_SOURCE_POSTHOC_REPRODUCTION_PLAN_NOT_ACCEPTANCE',archive_receipt_sha256=h(B/'RESULT.json'),
         context_sha256=h(C),host_resources=available,host_reserve_bytes=256*2**30,
         resource_policy='PV child256GiB cap; Gaussian4workers32GiB each; existing estimate caps unchanged; all below300GiB perrun. Shared generic libraries only, zero predecessor application bank.',
         source_isolation='Host source-cold relocation replay, not a namespace-isolated discovery experiment.',
         jobs=[dict(name=n,argv=list(map(str,a)),cpu_affinity=c)for n,a,c in jobs],late=[dict(name=n,argv=list(map(str,a)),cpu_affinity=affinity[16:20]) for n,a in late]))
    def execute(n,a,cpus):
        begin=time.monotonic();out=Q/(n+'.stdout');err=Q/(n+'.stderr');timing=Q/(n+'.time')
        argv=['taskset','-c',','.join(map(str,cpus)),'/usr/bin/time','-v','-o',str(timing)]+list(map(str,a))
        with out.open('xb')as o,err.open('xb')as e:p=subprocess.run(argv,stdout=o,stderr=e,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1'))
        result=dict(name=n,argv=argv,exitcode=p.returncode,seconds=time.monotonic()-begin,stdout_sha256=h(out),stderr_sha256=h(err),time_sha256=h(timing))
        if (Q/n/'RESULT.json').is_file():result.update(child_result_sha256=h(Q/n/'RESULT.json'),child_status=json.loads((Q/n/'RESULT.json').read_text()).get('status'))
        save(Q/(n+'-EXECUTION.json'),result)
        return result
    def late_chain():return [execute(n,a,affinity[16:20])for n,a in late]
    begin=time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=5)as pool:
        futures=[pool.submit(execute,n,a,c) for n,a,c in jobs]+[pool.submit(late_chain)]
        results=[]
        for f in concurrent.futures.as_completed(futures):
            x=f.result();results.extend(x if isinstance(x,list)else[x])
    passed=all(x['exitcode']==0 and str(x.get('child_status','')).startswith('PASS') for x in results)
    save(Q/'RESULT.json',dict(status='PASS_ALL_SEVEN_EXTRACTED_SOURCE_REPLAYS'if passed else'FAILED_EXTRACTED_SOURCE_REPLAY_PRESERVED',
        seconds=time.monotonic()-begin,jobs=results,plan_sha256=h(Q/'PLAN.json'),no_monolithic_all_lane_claim=True,
        original_results_unchanged=True,model_sessions_rerun=False))
    print(json.dumps(dict(status='PASS_ALL_SEVEN_EXTRACTED_SOURCE_REPLAYS'if passed else'FAILED',jobs=len(results),seconds=time.monotonic()-begin)))
    need(passed,'At least one relocated-source replay failed; retained logs')
if __name__=='__main__':main()
