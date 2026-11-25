#!/usr/bin/env python3
"""Clean-folder replay of the independent written explicit-window validation."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--slab-only',action='store_true')
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh replay directory required')
    here=Path(__file__).resolve().parent
    relative=['review_global_chord.py','review_applicability.py','inputs/certify_integer.py','inputs/witness-ap.json','inputs/w4.json']
    inputs=[dict(path=n,sha256=sha(here/n),bytes=(here/n).stat().st_size)for n in relative]
    avail=next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:'))
    need(avail>=(256+64)*2**30,'Preserve 256GiB host reserve outside 64GiB maximum child allowance')
    need(shutil.disk_usage(a.run.parent).free>=2**30,'At least1GiB separate free disk required for small reproducibility artifacts')
    a.run.mkdir(parents=True);source=a.run/'source';source.mkdir()
    for row in inputs:
        p=source/row['path'];p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(here/row['path'],p)
        need(sha(p)==row['sha256'],'Source snapshot identity')
    plan=dict(controller_sha256=sha(Path(__file__)),python=sys.version,inputs=inputs,mem_available_bytes=avail,
        memory_limit_bytes=64*2**30,host_reserve_bytes=256*2**30,free_disk_bytes=shutil.disk_usage(a.run).free,
        cpu_affinity=sorted(os.sched_getaffinity(0)),source_first_PV=False,lean_proof=False)
    (a.run/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    began=time.monotonic();steps=[]
    cases=[('Fap','slab',131072,'witness-ap.json')]
    if not a.slab_only:cases.append(('w4','ray',16777216,'w4.json'))
    for label,mode,grid,witness in cases:
        phases=[('numeric',[sys.executable,'-B',str(source/'review_global_chord.py'),'--fft-source',str(source/'inputs/certify_integer.py'),'--witness',str(source/'inputs'/witness),'--run',str(a.run/(label+'-numeric')),'--grid',str(grid),'--mode',mode]),
            ('applicability',[sys.executable,'-B',str(source/'review_applicability.py'),'--numerical-receipt',str(a.run/(label+'-numeric/RESULT.json')),'--fft-source',str(source/'inputs/certify_integer.py'),'--run',str(a.run/(label+'-applicability'))])]
        for phase,child in phases:
            name=label+'-'+phase;timefile=a.run/(name+'.time')
            command=['/usr/bin/time','-v','-o',str(timefile),'prlimit','--as='+str(64*2**30),'--',*child]
            start=time.monotonic()
            with(a.run/(name+'.stdout')).open('wb')as out,(a.run/(name+'.stderr')).open('wb')as err:
                p=subprocess.run(command,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
            need(p.returncode==0,'Replay child failed, exact evidence retained: '+name)
            times=timefile.read_text();match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',times)
            need(match is not None,'Actual RAM metric absent')
            receipt=a.run/(label+'-'+('numeric'if phase=='numeric'else'applicability'))/'RESULT.json'
            need(receipt.is_file(),'Missing child receipt')
            steps.append(dict(name=name,command=command,exit_code=p.returncode,seconds=time.monotonic()-start,
                maximum_rss_kib=int(match.group(1)),receipt_sha256=sha(receipt),time_sha256=sha(timefile),
                stdout_sha256=sha(a.run/(name+'.stdout')),stderr_sha256=sha(a.run/(name+'.stderr'))))
    for row in inputs:need(sha(here/row['path'])==sha(source/row['path'])==row['sha256'],'Source changed during replay')
    need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed during replay')
    result=dict(status='PASS_INDEPENDENT_EXPLICIT_SLAB_REPLAY_ONLY'if a.slab_only else'PASS_FULL_INDEPENDENT_EXPLICIT_SLAB_AND_RAY_REPLAY',
        seconds=time.monotonic()-began,steps=steps,maximum_child_rss_kib=max(x['maximum_rss_kib']for x in steps),
        retained_disk_bytes=sum(p.stat().st_size for p in a.run.rglob('*')if p.is_file()),oom_events=0,signal_kills=0,
        plan_sha256=sha(a.run/'PLAN.json'),source_first_PV=False,lean_proof=False,
        scope='Externally directed rational computations and independently reviewed written continuum proof; analytic and finite-gap source inputs remain explicit.')
    tmp=a.run/'RESULT.json.tmp';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,a.run/'RESULT.json');tmp.unlink()
    print(json.dumps({k:result[k]for k in ['status','seconds','maximum_child_rss_kib','retained_disk_bytes']}))

if __name__=='__main__':main()
