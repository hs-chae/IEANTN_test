#!/usr/bin/env python3
"""Strict continuation of an interrupted Fap source-cold verification.
Inherited source-cold receipts remain distinct from newly executed modules.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, time
from pathlib import Path
from reproduce_fap_fft_math import R, S, BAD, context, load, need, publish, sha, validate_forest

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True)
    ap.add_argument('--partial',type=Path,required=True)
    ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--memory-gib',type=int,default=128)
    a=ap.parse_args()
    need(a.memory_gib in (64,128,256,300),'Supported memory ceiling required')
    mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable']>=(a.memory_gib+256)*2**30,'256GiB host reserve required')
    need(not os.path.lexists(a.run),'Fresh continuation directory required')
    old=a.partial.resolve(strict=True)
    need(not(old/'RESULT.json').exists()and not(old/'FAILURE.json').exists(),'Only interrupted partial run accepted')
    interruption=load(old/'INTERRUPTION.json')
    need(interruption['status']=='INTERRUPTED_NO_ACCEPTANCE'and interruption['tool_session_exitcode']==143,'Expected recorded SIGTERM interruption')
    p=load(old/'PLAN.json');c=context(a.context,R)
    need(p['context_sha256']==sha(a.context),'Exact original dependency context required')
    need(p['controller_sha256']==sha(old/'driver.executed.py')==sha(S/'primal/reproduce_fap_fft_math.py'),'Original controller changed')
    base=Path(p['forest_base']);bp=validate_forest(base,c)
    need(p['forest_result_sha256']==sha(base/'RESULT.json')and p['forest_plan_sha256']==sha(base/'PLAN.json'),'Forest receipt changed')
    rows=p['additional_sources'];need(len(rows)==142 and len({r['module']for r in rows})==142,'Exact fixed 142-module closure required')
    inherited=[];missing=[]
    for row in rows:
        n=row['module'];tag=n.replace('.','_');rel=n.replace('.','/')
        need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'Source changed:'+n)
        receipt=old/(tag+'.COMPILED.json')
        if not receipt.exists():missing.append(row);continue
        q=load(receipt);need(q['module']==n and q['exitcode']==0,'Invalid completed receipt:'+n)
        for suffix in ('stdout','stderr','time'):
            need(sha(old/'logs'/(tag+'.'+suffix))==q[suffix+'_sha256'],'Log changed:'+n)
        need(BAD.search((old/'logs'/(tag+'.stdout')).read_text()+'\n'+(old/'logs'/(tag+'.stderr')).read_text())is None,'Compiler diagnostic:'+n)
        need(sha(old/'objects'/(rel+'.olean'))==q['object_sha256'],'Object changed:'+n)
        for artifact in q['object_artifacts']:
            need(not Path(artifact['path']).is_absolute()and'..'not in Path(artifact['path']).parts,'Unsafe artifact')
            need(sha(old/'objects'/artifact['path'])==artifact['sha256'],'Sidecar changed:'+n)
        inherited.append(dict(module=n,receipt=str(receipt),receipt_sha256=sha(receipt),source_sha256=row['source_sha256'],result=q))
    need(len(inherited)==interruption['completed_validated_modules']==123 and len(missing)==19,'Exact continuation lineage required')
    a.run.mkdir(parents=True)
    bank,frozen,logs=a.run/'objects',a.run/'source',a.run/'logs'
    for d in (bank,frozen,logs):d.mkdir()
    (a.run/'driver.executed.py').write_bytes(Path(__file__).read_bytes())
    (a.run/'original-driver.executed.py').write_bytes((old/'driver.executed.py').read_bytes())
    for path in(base/'objects').iterdir():
        need(path.is_file()and not path.is_symlink(),'Unexpected base artifact')
        shutil.copyfile(path,bank/path.name)
    for row in bp['sources']:
        if row['file'].endswith('.lean'):shutil.copyfile(base/'sources'/row['file'],frozen/row['file'])
    copied=[]
    for row in rows:
        target=frozen.joinpath(*row['module'].split('.')).with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(Path(row['snapshot']),target)
        copied.append(dict(row,snapshot=str(target)))
    for item in inherited:
        for artifact in item['result']['object_artifacts']:
            target=bank/artifact['path'];target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(old/'objects'/artifact['path'],target)
    plan=dict(status='RESUMED_SOURCE_COLD_LINEAGE_NOT_FRESH_UNINTERRUPTED_142',original_partial=str(old),original_plan_sha256=sha(old/'PLAN.json'),
        interruption_sha256=sha(old/'INTERRUPTION.json'),forest_base=str(base),forest_result_sha256=sha(base/'RESULT.json'),context_sha256=sha(a.context),
        inherited_modules=inherited,additional_sources=copied,newly_compiled_modules=[r['module']for r in missing],controller_sha256=sha(Path(__file__)),
        original_controller_sha256=p['controller_sha256'],memory_ceiling_gib=a.memory_gib,MemAvailable_bytes=mem['MemAvailable'],historical_application_fallback=False)
    publish(a.run/'PLAN.json',plan)
    env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);started=time.monotonic();new=[]
    for row in missing:
        n=row['module'];tag=n.replace('.','_');source=frozen.joinpath(*n.split('.')).with_suffix('.lean');obj=bank.joinpath(*n.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        out,err,tm=[logs/(tag+'.'+suffix)for suffix in('stdout','stderr','time')]
        cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.memory_gib*2**30),'--stack='+str(256*2**20),'--',c['compiler'],'-j1','--root='+str(frozen),'-o',str(obj),str(source)]
        t=time.monotonic()
        with out.open('x')as o,err.open('x')as e:result=subprocess.run(cmd,cwd=frozen,env=env,stdout=o,stderr=e)
        need(result.returncode==0 and BAD.search(out.read_text()+'\n'+err.read_text())is None,'Compiler failure/diagnostic:'+n)
        need(obj.is_file(),'Missing output:'+n)
        artifacts=[dict(path=str(q.relative_to(bank)),sha256=sha(q),bytes=q.stat().st_size)for q in sorted(obj.parent.glob(obj.name+'*'))if q.is_file()]
        item=dict(module=n,exitcode=0,seconds=time.monotonic()-t,command=cmd,source_sha256=sha(source),object_sha256=sha(obj),object_artifacts=artifacts,
            stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm))
        publish(a.run/(tag+'.COMPILED.json'),item);new.append(item)
    validate_forest(base,c)
    for row in copied:need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'Final source changed')
    for item in inherited:
        need(sha(Path(item['receipt']))==item['receipt_sha256'],'Inherited receipt changed')
        for art in item['result']['object_artifacts']:need(sha(bank/art['path'])==art['sha256'],'Inherited copied object changed')
    need(sha(Path(__file__))==plan['controller_sha256'],'Continuation controller changed')
    audit=(logs/'FapFFTKernelAudit.stdout').read_text()
    need('FAP_KERNEL_ANT_AUDIT_PASS roots=14 numerical_norm_premises=0 FFT_status=KERNEL_ONLY_NOT_PV'in audit,'Final typed ANT audit missing')
    peak=0
    for path in list(logs.glob('*.time'))+[old/'logs'/(q['module'].replace('.','_')+'.time')for q in inherited]:
        found=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',path.read_text())
        if found:peak=max(peak,int(found.group(1)))
    publish(a.run/'OBJECTS.json',[dict(path=str(q.relative_to(bank)),sha256=sha(q),bytes=q.stat().st_size)for q in sorted(bank.rglob('*'))if q.is_file()])
    publish(a.run/'RESULT.json',dict(status='PASS_FAP_FULL_FINITE_ANT_RESUMED_SOURCE_COLD_LINEAGE_KERNEL_ONLY',forest_modules=42,inherited_source_cold_modules=len(inherited),newly_compiled_modules=len(new),
        total_additional_modules=142,audited_roots=14,resume_seconds=time.monotonic()-started,inherited_compile_seconds=sum(q['result']['seconds']for q in inherited),max_additional_process_RSS_KiB=peak,
        disk_bytes=sum(q.stat().st_size for q in a.run.rglob('*')if q.is_file()),oom_or_sigkill_events=0,original_interruption_signal='SIGTERM',fresh_uninterrupted_142_claim=False,numerical_norm_premises=0,
        source_first_FFT_PV_complete=False,plan_sha256=sha(a.run/'PLAN.json')))
    print((a.run/'RESULT.json').read_text())
if __name__=='__main__':main()
