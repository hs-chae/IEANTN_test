#!/usr/bin/env python3
"""One pure comparison source plus full theorem audit above validated723.

Kernel proof checking, not source-first program verification. Run the documented
complete clean723 pipeline first; no developer application cache is accepted.
"""
from pathlib import Path
import argparse, importlib.util, json, math, os, re, shutil, subprocess, threading, time
H=Path(__file__).resolve().parent
R=H.parents[2]
QPATH=H.parent/'integration/ram606/reproduce.py'
spec=importlib.util.spec_from_file_location('accepted723',QPATH)
Q=importlib.util.module_from_spec(spec);spec.loader.exec_module(Q)
need,sha,read,save=Q.need,Q.sha,Q.read,Q.save
SOURCE_SHA='d971406964dbefac469806bcf2215550d7c8622bdbf3113463690b9d7f16f90e'
AUDIT='''import BoxVsLee
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, i) in env.const2ModIdx.toList do
    if (env.header.moduleNames[i.toNat]?).getD .anonymous != `BoxVsLee then continue
    let some ci := env.find? n | continue
    if !ci.isTheorem then continue
    let axs ← collectAxioms n
    unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains) do
      throwError "Nonstandard axiom: {n}: {axs}"
    logInfo m!"BOX_LEE_THEOREM {Json.compress (Json.mkObj [(\"name\",toJson n.toString),(\"axioms\",toJson (axs.map Name.toString))])}"
    count := count + 1
  unless count == 15 do throwError "Expected all fifteen actual theorem constants: {count}"
  logInfo m!"BOX_LEE_ALL15_PASS"
'''

WRITTEN_THEOREMS={'RHOcticPush.BoxLeeComparison.'+n for n in [
    'log_lower','exp_cubic','cubic12_positive','cubic11_positive',
    'scaled12_positive','scaled11_positive','box_lt_lee11','box_lt_lee12','box_lt_both']}

def payload(text):
    def pairs(rows):
        d={}
        for k,v in rows:
            need(k not in d,'duplicate JSON payload key');d[k]=v
        return d
    def finite(t):
        x=float(t);need(math.isfinite(x),'nonfinite JSON float');return x
    return json.loads(text,object_pairs_hook=pairs,parse_float=finite,
                      parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite JSON')))

def gnu_seconds(text):
    m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)',text)
    need(m is not None,'actual GNU time wall clock');v=m[1].split(':')
    need(len(v) in [2,3],'GNU time format')
    out=0.0
    for x in v:out=60*out+float(x)
    need(math.isfinite(out) and out>=0,'finite GNU elapsed')
    return out

def metrics(run,r):
    for k in ['peak_individual_child_RSS_KiB','sampled_peak_process_tree_RSS_bytes',
              'sampled_peak_owned_disk_bytes','total_source_modules']:
        need(type(r[k]) is int and r[k]>=0,'exact integer summary:'+k)
    need(r['total_source_modules']==725,'723+one comparison+one audit')
    for k in ['seconds','observed_controller_wall_seconds']:
        need(type(r[k]) in [int,float] and math.isfinite(r[k]) and r[k]>=0,'finite measured time')
    need(r['RESOURCE_ADMISSION_sha256']==sha(run/'RESOURCE_ADMISSION.json'),'admission binding')
    ad=read(run/'RESOURCE_ADMISSION.json')
    need(all(type(ad[k]) is int for k in ['MemAvailable_bytes','per_job_AS_bytes','host_reserve_bytes','free_disk_bytes']),'admission integers')
    need(ad['per_job_AS_bytes']==64*(1<<30) and ad['host_reserve_bytes']==512*(1<<30)
         and ad['MemAvailable_bytes']>=ad['per_job_AS_bytes']+ad['host_reserve_bytes']
         and ad['free_disk_bytes']>=10*(1<<30),'actual resource admission')
    need(r['TREE_RSS_sha256']==sha(run/'TREE_RSS.csv'),'resource sample identity')
    ls=(run/'TREE_RSS.csv').read_text().splitlines()
    need(ls[0]=='seconds,process_tree_RSS_bytes,process_count,owned_disk_bytes' and len(ls)>1,'complete resource sample')
    parsed=[]
    for line in ls[1:]:
        x=line.split(',');need(len(x)==4,'sample columns')
        t=float(x[0]);need(math.isfinite(t) and t>=0,'sample time')
        need(all(re.fullmatch(r'[0-9]+',q) is not None for q in x[1:]),'integer resource samples')
        parsed.append([t,*[int(q) for q in x[1:]]])
    need(max(q[1] for q in parsed)==r['sampled_peak_process_tree_RSS_bytes'],'aggregate RSS sample')
    need(max(q[3] for q in parsed)==r['sampled_peak_owned_disk_bytes']<=300*(1<<30),'sampled disk/cap')
    need(Q.Z.Q.disk(run)<=300*(1<<30),'actual final scratch cap')

def basis_maps(root):
    rr=Q.validate(root)
    maps,b=Q.foundation_maps(Path(rr['foundation']['root']))
    for row in read(Path(root)/'BUILD.json')['modules']:
        p=Path(root)/'objects'/(row['module'].replace('.','/')+'.olean')
        need(sha(p)==row['object_sha256'],'basis object hash')
        need(row['module'] not in maps,'basis namespace')
        maps[row['module']]={'object':p,'object_sha256':row['object_sha256']}
    need(len(maps)==723,'complete validated723')
    return maps,{'root':str(Path(root).resolve()),'RESULT_sha256':sha(Path(root)/'RESULT.json')}

def validate(root,candidate=None):
    root=Path(root).resolve();r=read(candidate or root/'RESULT.json')
    need(r['status']=='PASS_FRESH_BOX_VS_TWO_LEE_FUNCTIONS','result')
    need(r['controller_sha256']==sha(__file__)==sha(root/'reproduce.executed.py'),'controller pin')
    need(r['basis_controller_sha256']==sha(QPATH),'basis validator pin')
    metrics(root,r)
    maps,basis=basis_maps(r['foundation']['root']);need(basis==r['foundation'],'foundation')
    need(sha(H/'BoxVsLee.lean')==SOURCE_SHA,'scientific source freeze')
    ctx=Q.Z.Q.P.context();ex=Path(r['execution_root'])
    need(r['compiler_sha256']==ctx['compiler_sha256'],'compiler')
    need([x['module'] for x in r['compilations']]==['BoxVsLee','BoxLeeAudit'],'complete two routes')
    generic=[Path(x).resolve() for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
    for row in r['compilations']:
        mod=row['module'];src=root/'source'/(mod+'.lean');obj=root/'objects'/(mod+'.olean')
        need(not src.is_symlink() and not obj.is_symlink(),'regular new artifacts')
        want=SOURCE_SHA if mod=='BoxVsLee' else __import__('hashlib').sha256(AUDIT.encode()).hexdigest()
        need(sha(src)==row['source_sha256']==want and sha(obj)==row['object_sha256'],'source/object')
        need(type(row['returncode']) is int and row['returncode']==0,'compiler success')
        need(row['command']==Q.compile_command(ctx,ex,mod,64*(1<<30),2),'exact execution command')
        for x in ['stdout','stderr']:
            need(sha(root/'logs'/(mod+'.'+x))==row[x+'_sha256'],'actual compiler log')
        rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(root/'logs'/(mod+'.stderr')).read_text())
        need(rss is not None and type(row['peak_RSS_KiB']) is int and row['peak_RSS_KiB']==int(rss[1]),'actual child RSS')
        need(type(row['seconds']) in [int,float] and math.isfinite(row['seconds']) and row['seconds']==gnu_seconds((root/'logs'/(mod+'.stderr')).read_text()),'actual GNU wall time')
        maps[mod]={'object':obj,'object_sha256':row['object_sha256']}
    out=(root/'logs/BoxLeeAudit.stdout').read_text()
    rows=[payload(x.split('BOX_LEE_THEOREM ',1)[1]) for x in out.splitlines() if 'BOX_LEE_THEOREM {' in x]
    need(out.count('BOX_LEE_ALL15_PASS')==1 and len(rows)==15 and len({x['name'] for x in rows})==15,'all15 actual theorem constants')
    need(WRITTEN_THEOREMS <= {x['name'] for x in rows},'all9 written theorem identities')
    need(max(x['peak_RSS_KiB'] for x in r['compilations'])==r['peak_individual_child_RSS_KiB'],'individual RSS maximum')
    need(sum(x['seconds'] for x in r['compilations'])==r['seconds']<=r['observed_controller_wall_seconds']+1,'actual compilation elapsed')
    need(all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in rows),'all axioms')
    need([x['module'] for x in r['dependency_probes']]==['BoxVsLee','BoxLeeAudit'],'all probes')
    bypath={v['object'].resolve():v['object_sha256'] for v in maps.values()}
    for row in r['dependency_probes']:
        mod=row['module']
        need(type(row['returncode']) is int and row['returncode']==0,'actual deps success')
        need(row['command']==[ctx['compiler'],'--root='+str(ex/'source'),'--deps',str(ex/'source'/(mod+'.lean'))],'deps command')
        for x in ['stdout','stderr']:
            need(sha(root/'dependencies'/(mod+'.'+x))==row[x+'_sha256'],'deps log')
        paths=[Path(x).resolve() for x in (root/'dependencies'/(mod+'.stdout')).read_text().splitlines()]
        need(bool(paths),'nonempty actual deps')
        seen=set()
        for p in paths:
            if p.is_relative_to(ex):p=(root/p.relative_to(ex)).resolve()
            seen.add(p)
            if any(p.is_relative_to(g) for g in generic):continue
            need(p in bypath and sha(p)==bypath[p],'foreign object')
        expected=maps['IEANTN.Vocabulary.RHOcticEvolution' if mod=='BoxVsLee' else 'BoxVsLee']['object'].resolve()
        need(expected in seen,'actual direct app import')
    need(r['source_first_PV_claim'] is False and r['DEV_objects_used'] is False,'trust boundaries')
    need(type(r['observed_process_OOM_events']) is int and r['observed_process_OOM_events']==0,'success is not OOM')
    return r

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--foundation',type=Path);p.add_argument('--out',type=Path);p.add_argument('--verify',type=Path);a=p.parse_args()
    if a.verify:
        need(a.foundation is None and a.out is None,'exclusive readback');validate(a.verify);print('PASS_BOX_LEE_READBACK');return
    need(a.foundation is not None and a.out is not None,'foundation/out required')
    need(sha(H/'BoxVsLee.lean')==SOURCE_SHA,'frozen scientific source')
    maps,basis=basis_maps(a.foundation);ctx=Q.Z.Q.P.context();out=a.out.resolve()
    need(not out.exists() and out.parent.is_dir(),'fresh owned output')
    avail=Q.Z.Q.available();need(avail>=(512+64)*(1<<30),'host reserve512GiB plus64GiB job')
    need(shutil.disk_usage(out.parent).free>=10*(1<<30),'independent disk admission')
    out.mkdir()
    for n in ['source','objects','union','logs','dependencies']:(out/n).mkdir()
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    (out/'source/BoxVsLee.lean').write_bytes((H/'BoxVsLee.lean').read_bytes());(out/'source/BoxLeeAudit.lean').write_text(AUDIT)
    save(out/'RESOURCE_ADMISSION.json',{'MemAvailable_bytes':avail,'per_job_AS_bytes':64*(1<<30),'host_reserve_bytes':512*(1<<30),'free_disk_bytes':shutil.disk_usage(out.parent).free})
    for m,x in maps.items():
        l=out/'union'/(m.replace('.','/')+'.olean');l.parent.mkdir(parents=True,exist_ok=True);l.symlink_to(x['object'])
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'union'),*ctx['generic_libraries']])
    rows=[];probes=[];start=time.monotonic();stats={'peak_RSS_bytes':0,'peak_disk_bytes':0,'last_disk':0,'samples':0};stop=threading.Event()
    monitor=threading.Thread(target=Q.Z.Q.monitor,args=(out,stop,stats),daemon=True);monitor.start()
    try:
        for mod in ['BoxVsLee','BoxLeeAudit']:
            cmd=Q.compile_command(ctx,out,mod,64*(1<<30),2);t=time.monotonic()
            with (out/'logs'/(mod+'.stdout')).open('w') as fo,(out/'logs'/(mod+'.stderr')).open('w') as fe:
                cp=subprocess.run(cmd,env=env,cwd=out/'source',stdout=fo,stderr=fe)
            row={'module':mod,'command':cmd,'returncode':cp.returncode,'seconds':gnu_seconds((out/'logs'/(mod+'.stderr')).read_text()),'source_sha256':sha(out/'source'/(mod+'.lean'))}
            for x in ['stdout','stderr']:row[x+'_sha256']=sha(out/'logs'/(mod+'.'+x))
            rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(out/'logs'/(mod+'.stderr')).read_text());need(rss is not None,'child RSS')
            row['peak_RSS_KiB']=int(rss[1]);rows.append(row);save(out/'BUILD.json',rows)
            need(cp.returncode==0,'actual Lean failure preserved')
            obj=out/'objects'/(mod+'.olean');row['object_sha256']=sha(obj);(out/'union'/(mod+'.olean')).symlink_to(obj)
            dcmd=[ctx['compiler'],'--root='+str(out/'source'),'--deps',str(out/'source'/(mod+'.lean'))]
            cp=subprocess.run(dcmd,env=env,cwd=out/'source',capture_output=True,text=True)
            pr={'module':mod,'command':dcmd,'returncode':cp.returncode}
            for x,txt in [('stdout',cp.stdout),('stderr',cp.stderr)]:
                f=out/'dependencies'/(mod+'.'+x);f.write_text(txt);pr[x+'_sha256']=sha(f)
            probes.append(pr);need(cp.returncode==0,'deps failure')
    finally:stop.set();monitor.join()
    need('monitor_error' not in stats and stats['samples']>0,'actual complete resource monitor')
    r={'status':'PASS_FRESH_BOX_VS_TWO_LEE_FUNCTIONS','execution_root':str(out),'controller_sha256':sha(__file__),'basis_controller_sha256':sha(QPATH),'foundation':basis,'compiler_sha256':ctx['compiler_sha256'],'compilations':rows,'dependency_probes':probes,'seconds':sum(x['seconds'] for x in rows),'observed_controller_wall_seconds':time.monotonic()-start,'total_source_modules':725,'RESOURCE_ADMISSION_sha256':sha(out/'RESOURCE_ADMISSION.json'),'TREE_RSS_sha256':sha(out/'TREE_RSS.csv'),'peak_individual_child_RSS_KiB':max(x['peak_RSS_KiB'] for x in rows),'sampled_peak_process_tree_RSS_bytes':stats['peak_RSS_bytes'],'sampled_peak_owned_disk_bytes':stats['peak_disk_bytes'],'source_first_PV_claim':False,'DEV_objects_used':False,'observed_process_OOM_events':0}
    save(out/'CANDIDATE.json',r);validate(out,out/'CANDIDATE.json')
    save(out/'RESULT.json',r);print('PASS_FRESH_BOX_VS_TWO_LEE_FUNCTIONS')
if __name__=='__main__':main()
