#!/usr/bin/env python3
"""Exhaustive fixed endpoint/log/cell kernel verification, development phase.
A separate fresh source-closure replay removes development application banks.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent;R=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,r):
    q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'Unexpected pending receipt')
    q.write_text(json.dumps(r,indent=2)+'\n');os.replace(q,p)
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--foundation',type=Path,required=True);p.add_argument('--pilot',type=Path,required=True);p.add_argument('--jobs',type=int,default=8);a=p.parse_args()
    need(1<=a.jobs<=8,'Bounded jobs');need(not a.out.exists(),'Fresh batch output required')
    available=next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:'))
    need(available >= (512+64*a.jobs)*(1<<30),'Host memory reserve')
    disk=shutil.disk_usage(a.out.parent).free;need(disk>=1<<40,'Independent scratch allowance requires1TiB free')
    ctx=json.loads((R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text());need(sha(ctx['compiler'])==ctx['compiler_sha256'],'Compiler identity')
    foundations=[a.foundation/n/'objects'for n in ['cell-data-v1','log-data-v2','data-v3','checker-v4']]
    for f in foundations:need(f.is_dir(),'Missing explicit development foundation')
    frozen={str(HERE/(m+'.lean')):sha(HERE/(m+'.lean'))for m in ['OcticEndpointChecker','OcticEndpointData','OcticLogEndpointData','OcticCellData']}
    frozen.update({str(HERE/f'OcticEndpointBlock{i:03d}.lean'):sha(HERE/f'OcticEndpointBlock{i:03d}.lean')for i in range(115)})
    a.out.mkdir(parents=True);save(a.out/'FROZEN_INPUTS.json',dict(sources=frozen,compiler_sha256=ctx['compiler_sha256'],classification='Ordinary kernel certificates, NOT source-first PV'))
    save(a.out/'RESOURCES.json',dict(MemAvailable_bytes=available,free_disk_bytes=disk,per_run_AS_GiB=64,jobs=a.jobs,host_reserve_GiB=512,scratch_allowance_GiB=300,cpus=list(range(88,88+a.jobs))))
    started=time.monotonic();commands=[]
    for i in range(1,115):
        cmd=['taskset','-c',str(88+(i-1)%a.jobs),sys.executable,str(R/'Solutions/RHOcticPush.v1/scripts/dev_compile.py'),'--source',str(HERE/f'OcticEndpointBlock{i:03d}.lean'),'--out',str(a.out/f'block{i:03d}')]
        for f in foundations:cmd+=['--bank',str(f)]
        commands.append(cmd)
    save(a.out/'COMMANDS.json',commands)
    def lane(k):
        for j in range(k,len(commands),a.jobs):
            run=subprocess.run(commands[j],capture_output=True,text=True)
            (a.out/f'controller-{j+1:03d}.stdout').write_text(run.stdout)
            (a.out/f'controller-{j+1:03d}.stderr').write_text(run.stderr)
            need(run.returncode==0,'Kernel block failed:'+str(j+1))
            print('PASS_BLOCK',j+1,flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as ex:
        fs=[ex.submit(lane,k)for k in range(a.jobs)]
        for f in fs:f.result()
    rows=[]
    for i in range(115):
        d=a.pilot if i==0 else a.out/f'block{i:03d}';receipt=d/'RECEIPT.json';rr=json.loads(receipt.read_text());source=HERE/f'OcticEndpointBlock{i:03d}.lean';obj=d/'objects'/f'OcticEndpointBlock{i:03d}.olean'
        need(rr['status']=='PASS_DEV'and type(rr['returncode'])is int and rr['returncode']==0,'Incomplete block')
        need(rr['source_sha256']==sha(source)==frozen[str(source)],'Block source drift')
        names=[f'RHOcticPush.Moments.Endpoint.checked{i:03d}']+(['RHOcticPush.Moments.Endpoint.checked_last']if i==114 else[])
        need({x['name']for x in rr['axioms']}==set(names),'Complete actual axiom checks')
        for x in rr['axioms']:need(set(t.strip()for t in x['axioms'].split(',')if t.strip())<=ALLOWED,'Native/nonstandard axiom')
        stderr=(d/'stderr').read_text();rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',stderr);need(rss is not None,'Missing actual RAM observation')
        rows.append(dict(block=i,receipt=str(receipt),receipt_sha256=sha(receipt),source_sha256=sha(source),object=str(obj),object_sha256=sha(obj),stdout_sha256=sha(d/'stdout'),stderr_sha256=sha(d/'stderr'),seconds=rr['wall_seconds'],peak_RSS_KiB=int(rss[1])))
    for f,h in frozen.items():need(sha(f)==h,'Frozen input changed during batch')
    disk_owned=sum(p.stat().st_size for p in a.out.rglob('*')if p.is_file());need(disk_owned<=300*(1<<30),'Owned scratch allowance')
    result=dict(status='PASS_ALL_7301_ROWS_7300_CELLS_KERNEL_DEV',blocks=115,rows=7301,cells=7300,records=rows,seconds=time.monotonic()-started,peak_child_RSS_KiB=max(r['peak_RSS_KiB']for r in rows),disk_owned_bytes=disk_owned,source_first_PV=False,native_execution_axioms=False,observed_process_OOM_events=0,OOM_evidence='All115 accepted Lean invocations returned0; no host-wide attribution',fresh_full_source_closure=False,trust='Development application banks reused; final complete source-only replay separately required')
    save(a.out/'RESULT.json',result);save(HERE/'BLOCK_RESULTS.json',result);print(result['status'])
if __name__=='__main__':main()
