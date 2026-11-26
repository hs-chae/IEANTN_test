#!/usr/bin/env python3
"""Fresh canonical consumers over a fully revalidated source-cold Fap math base.
The numerical FFT remains kernel-only. No historical/unvalidated app fallback.
"""
import argparse,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
S=HERE.parents[1]
R=S.parents[1]
sys.path.insert(0,str(S/'primal'))
from reproduce_fap_fft_math import BAD,GENERIC,context,load,need,publish,sha,validate_forest

def relative(root,name):
    p=Path(name)
    need(not p.is_absolute()and'..'not in p.parts,'Unsafe artifact path')
    q=root/p
    need(q.is_file()and not q.is_symlink(),'Missing regular artifact:'+str(q))
    return q

def validate_math(base,c,context_path):
    p,r=load(base/'PLAN.json'),load(base/'RESULT.json')
    need(not(base/'FAILURE.json').exists(),'Failed math base')
    resumed=r['status']=='PASS_FAP_FULL_FINITE_ANT_RESUMED_SOURCE_COLD_LINEAGE_KERNEL_ONLY'
    need(resumed or r['status']=='PASS_FAP_FFT_NORM_AND_FULL_FINITE_ANT_KERNEL_ONLY','Unaccepted mathematical base')
    need(r['forest_modules']==42 and r['audited_roots']==14 and r['numerical_norm_premises']==0,'Wrong math proof scope')
    need(r['oom_or_sigkill_events']==0 and r['source_first_FFT_PV_complete']is False,'Wrong trust/resource claim')
    need(p['context_sha256']==sha(context_path),'Exact dependency context required')
    need(p['controller_sha256']==sha(base/'driver.executed.py'),'Executed math controller changed')
    if resumed:need(r['plan_sha256']==sha(base/'PLAN.json'),'Resumed math plan changed')
    forest=Path(p['forest_base']);fp=validate_forest(forest,c)
    need(p['forest_result_sha256']==sha(forest/'RESULT.json'),'Forest result changed')
    rows=p['additional_sources']
    need(len(rows)==142 and len({q['module']for q in rows})==142,'Expected fixed142 mathematical sources')
    inherited={}
    if resumed:
        need(r['inherited_source_cold_modules']==123 and r['newly_compiled_modules']==19,'Wrong continuation lineage')
        old=Path(p['original_partial'])
        need(sha(old/'PLAN.json')==p['original_plan_sha256']and sha(old/'INTERRUPTION.json')==p['interruption_sha256'],'Interrupted lineage changed')
        need(load(old/'INTERRUPTION.json')['status']=='INTERRUPTED_NO_ACCEPTANCE','Missing preserved interruption')
        inherited={q['module']:q for q in p['inherited_modules']}
        need(len(inherited)==123,'Wrong inherited receipt population')
    for row in rows:
        n=row['module'];tag=n.replace('.','_')
        need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'Math source changed:'+n)
        directory=base
        if n in inherited:
            item=inherited[n];receipt=Path(item['receipt']);directory=receipt.parent
            need(sha(receipt)==item['receipt_sha256'],'Inherited receipt changed:'+n)
        else:receipt=base/(tag+'.COMPILED.json')
        q=load(receipt);need(q['module']==n and q['exitcode']==0,'Invalid math compilation:'+n)
        need(sha(base/'objects'/(n.replace('.','/')+'.olean'))==q['object_sha256'],'Math object changed:'+n)
        for art in q['object_artifacts']:need(sha(relative(base/'objects',art['path']))==art['sha256'],'Math sidecar changed:'+n)
        for suffix in ['stdout','stderr','time']:
            need(sha(directory/'logs'/(tag+'.'+suffix))==q[suffix+'_sha256'],'Math log changed:'+n)
        need(BAD.search((directory/'logs'/(tag+'.stdout')).read_text()+'\n'+(directory/'logs'/(tag+'.stderr')).read_text())is None,'Math diagnostic:'+n)
    objects=load(base/'OBJECTS.json')
    need(len(objects)==184 and len({q['path']for q in objects})==184,'Expected exact184-object source-cold bank')
    for q in objects:need(sha(relative(base/'objects',q['path']))==q['sha256'],'Math bank inventory changed')
    audit=(base/'logs/FapFFTKernelAudit.stdout').read_text()
    need('FAP_KERNEL_ANT_AUDIT_PASS roots=14 numerical_norm_premises=0 FFT_status=KERNEL_ONLY_NOT_PV'in audit,'Typed numerical/ANT gate missing')
    return p,fp,objects

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True)
    ap.add_argument('--math-base',type=Path)
    ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--memory-gib',type=int,default=128)
    ap.add_argument('--preflight-only',action='store_true')
    a=ap.parse_args()
    need(a.memory_gib in(64,128,256,300),'Supported memory ceiling required')
    need(not os.path.lexists(a.run),'Fresh run required')
    c=context(a.context,R)
    mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable']>=(a.memory_gib+256)*2**30,'256GiB host reserve required')
    a.run.mkdir(parents=True)
    if a.math_base is None:
        need(not a.preflight_only,'Preflight requires existing accepted math base')
        a.math_base=a.run/'math-base'
        command=[sys.executable,str(S/'primal/reproduce_fap_fft_math.py'),'--context',str(a.context),'--run',str(a.math_base),'--memory-gib',str(a.memory_gib)]
        with(a.run/'math.stdout').open('x')as out,(a.run/'math.stderr').open('x')as err:z=subprocess.run(command,stdout=out,stderr=err)
        need(z.returncode==0,'Full source-cold numerical/ANT regeneration failed')
    base=a.math_base.resolve(strict=True);bp,fp,objects=validate_math(base,c,a.context)
    if a.preflight_only:
        publish(a.run/'RESULT.json',{'status':'PASS_PREFLIGHT_ONLY_NO_NEW_PROOF','validated_base_objects':184,'numerical_status':'KERNEL_ONLY_NOT_C_FFT_PV'})
        return
    bank,frozen,logs=[a.run/n for n in ['objects','source','logs']]
    for q in [bank,frozen,logs]:q.mkdir()
    for q in objects:
        dst=bank/q['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(base/'objects'/q['path'],dst)
    seen={q['module']for q in bp['additional_sources']}|{q['file'][:-5]for q in fp['sources']if q['file'].endswith('.lean')}
    active=set();rows=[]
    roots=[HERE,R]
    def visit(name):
        if name in seen or any(name==g or name.startswith(g+'.')for g in GENERIC):return
        need(name not in active,'Import cycle:'+name);active.add(name)
        src=next((p for root in roots if(p:=root.joinpath(*name.split('.')).with_suffix('.lean')).is_file()),None)
        need(src is not None and src.resolve().is_relative_to(R),'Missing canonical source:'+name)
        imports=[v for line in src.read_text().splitlines()if line.startswith('import ')for v in line[7:].split('--',1)[0].split()]
        for dep in imports:visit(dep)
        dst=frozen.joinpath(*name.split('.')).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
        rows.append(dict(module=name,origin=str(src),snapshot=str(dst),source_sha256=sha(src),imports=imports));seen.add(name);active.remove(name)
    visit('FiniteCanonicalAudit')
    plan=dict(status='SOURCE_COLD_CANONICAL_EXTENSION_OF_VALIDATED_184_MODULE_MATH_BASE',context_sha256=sha(a.context),controller_sha256=sha(Path(__file__)),
        base=str(base),base_result_sha256=sha(base/'RESULT.json'),base_plan_sha256=sha(base/'PLAN.json'),inherited_modules=184,sources=rows,
        historical_application_fallback=False,memory_ceiling_gib=a.memory_gib,MemAvailable_bytes=mem['MemAvailable'])
    (a.run/'driver.executed.py').write_bytes(Path(__file__).read_bytes());publish(a.run/'PLAN.json',plan)
    env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);started=time.monotonic();peak=0
    for row in rows:
        n=row['module'];tag=n.replace('.','_');out,err,tm=[logs/(tag+'.'+s)for s in['stdout','stderr','time']];obj=bank.joinpath(*n.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.memory_gib*2**30),'--stack='+str(256*2**20),'--',c['compiler'],'-j1','--root='+str(frozen),'-o',str(obj),row['snapshot']]
        t=time.monotonic()
        with out.open('x')as o,err.open('x')as e:z=subprocess.run(cmd,env=env,cwd=frozen,stdout=o,stderr=e)
        need(z.returncode==0 and BAD.search(out.read_text()+'\n'+err.read_text())is None,'Compiler failure/diagnostic:'+n)
        artifacts=[dict(path=str(q.relative_to(bank)),sha256=sha(q),bytes=q.stat().st_size)for q in sorted(obj.parent.glob(obj.name+'*'))if q.is_file()]
        need(bool(artifacts)and obj.is_file(),'Missing object:'+n)
        receipt=dict(module=n,exitcode=0,seconds=time.monotonic()-t,command=cmd,source_sha256=sha(Path(row['snapshot'])),object_sha256=sha(obj),object_artifacts=artifacts,
            stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm));publish(a.run/(tag+'.COMPILED.json'),receipt)
        m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm.read_text());need(m is not None,'Missing actual RAM receipt');peak=max(peak,int(m.group(1)))
    validate_math(base,c,a.context)
    for row in rows:need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'Final source changed')
    need(sha(Path(__file__))==plan['controller_sha256'],'Final controller changed')
    audit=(logs/'FiniteCanonicalAudit.stdout').read_text();need('FINITE_CANONICAL_AUDIT_PASS roots=8'in audit,'Typed canonical gate missing')
    publish(a.run/'OBJECTS.json',[dict(path=str(q.relative_to(bank)),sha256=sha(q),bytes=q.stat().st_size)for q in sorted(bank.rglob('*'))if q.is_file()])
    publish(a.run/'RESULT.json',dict(status='PASS_CANONICAL_FINITE_NODES_SOURCE_COLD_EXTENSION_KERNEL_ONLY',inherited_source_cold_objects=184,new_source_cold_modules=len(rows),
        typed_audited_roots=8,seconds=time.monotonic()-started,new_peak_RSS_KiB=peak,new_disk_bytes=sum(q.stat().st_size for q in a.run.rglob('*')if q.is_file()),oom_or_sigkill_events=0,
        full_C_FFT_PV_complete=False,official_Comparator_receipt=False,plan_sha256=sha(a.run/'PLAN.json')))
    print((a.run/'RESULT.json').read_text())
if __name__=='__main__':main()
