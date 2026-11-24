#!/usr/bin/env python3
"""Cold additive replay above the independently validated current primary454.
Independent DAG leaves run in bounded lanes. Final acceptance is fail-closed,
including under python -O/-OO; accepted application caches are never generic.
"""
from pathlib import Path
import argparse, concurrent.futures as cf, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, threading, time
HERE=Path(__file__).resolve().parent;I=HERE.parent;S=I.parent;R=S.parents[1]
spec=importlib.util.spec_from_file_location('primary_replay',I/'corrected/reproduce.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
need=P.need;sha=P.sha;read=P.read;save=P.save
sys.path.insert(0,str(HERE))
from resume_dag import validate_reuse, copy_reuse
def manifest_check(path):
 need(sha(path)==sha(HERE/'capture/SOURCE_CLOSURE.json'),'not immutable registered supplement manifest');m=read(path)
 need(m['schema']=='RH_OCTIC_SUPPLEMENT_SOURCE_CLOSURE_V1' and m['primary_modules']==454,'supplement schema')
 need(m['primary_manifest_sha256']==sha(I/'corrected/capture/SOURCE_CLOSURE.json'),'primary source freeze identity')
 need(m['selector_sha256']==sha(HERE/'prepare.py'),'supplement selector identity')
 for q in m['canonical_metadata']:need(sha(R/q['path'])==q['sha256'],'canonical metadata drift')
 need(sha(R/m['endpoint_freeze_path'])==m['endpoint_freeze_sha256'],'128 numerical source identity')
 pm=P.manifest_check(I/'corrected/capture/SOURCE_CLOSURE.json');done={x['module']for x in pm['modules']}
 for b in pm['baseline_manifests']:done.update(x['module']for x in read(R/b['path'])['modules'])
 need(len(done)==454,'complete primary454 required')
 for row in m['modules']:
  need(row['module']not in done and set(row['application_imports'])<=done,'supplement namespace/order/closure')
  need(sha(R/row['path'])==row['sha256'],'frozen supplement source drift:'+row['module'])
  if row['original_path']is not None:need(sha(R/row['original_path'])==row['sha256'],'current supplement source drift:'+row['module'])
  need('.Challenge'not in row['module'],'admitted source');done.add(row['module'])
 ep=read(R/m['endpoint_freeze_path']);need(len(ep['modules'])==128 and {x['module']for x in ep['modules']}<=done,'complete numerical128')
 need(len(m['roots'])==len(set(m['roots'])) and set(m['roots'])<=done,'probe root inventory')
 return m
def primary_maps(root):
 root=Path(root).resolve();r=P.validate(root);maps,fr=P.validate_foundation(r['foundation']['root']);pm=read(root/'SOURCE_CLOSURE.executed.json');b=read(root/'BUILD.json')
 for want,got in zip(pm['modules'],b['modules']):maps[want['module']]={'object':root/'objects'/(want['module'].replace('.','/')+'.olean'),'object_sha256':got['object_sha256']}
 need(len(maps)==454,'exact source-fresh primary454');return maps,{'root':str(root),'RESULT_sha256':sha(root/'RESULT.json'),'BUILD_sha256':sha(root/'BUILD.json'),'manifest_sha256':sha(root/'SOURCE_CLOSURE.executed.json')}
def disk(root):
 total=0
 for p in root.rglob('*'):
  try:
   if p.is_file()and not p.is_symlink():total+=p.stat().st_size
  except FileNotFoundError:pass # concurrent atomic log/object/receipt rename
 return total
def available():return next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:'))
def sample_tree(pid):
 table={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   fields=(p/'stat').read_text().rsplit(')',1)[1].split();ppid=int(fields[1]);rss=0
   for line in (p/'status').read_text().splitlines():
    if line.startswith('VmRSS:'):rss=int(line.split()[1])*1024;break
   table[int(p.name)]=(ppid,rss)
  except (OSError,ValueError,IndexError):continue
 descendants={pid};changed=True
 while changed:
  changed=False
  for child,(parent,rss)in table.items():
   if parent in descendants and child not in descendants:descendants.add(child);changed=True
 return sum(table.get(p,(0,0))[1]for p in descendants),len(descendants)
def monitor_inner(out,stop,stats):
 with (out/'TREE_RSS.csv').open('w')as f:
  f.write('seconds,process_tree_RSS_bytes,process_count,owned_disk_bytes\n');start=time.monotonic();n=0
  while not stop.is_set():
   rss,count=sample_tree(os.getpid());used=disk(out)if n%10==0 else stats['last_disk'];stats['last_disk']=used;stats['peak_RSS_bytes']=max(stats['peak_RSS_bytes'],rss);stats['peak_disk_bytes']=max(stats['peak_disk_bytes'],used);stats['samples']+=1;f.write(f'{time.monotonic()-start:.6f},{rss},{count},{used}\n');f.flush();n+=1;stop.wait(.5)
def monitor(out,stop,stats):
 try:monitor_inner(out,stop,stats)
 except BaseException as ex:stats['monitor_error']=repr(ex)

def command(ctx,run,mod,memory,threads):
 rel=mod.replace('.','/');return ['/usr/bin/prlimit','--as='+str(memory),'--','/usr/bin/time','-v',ctx['compiler'],'--root='+str(run/'source'),'-j'+str(threads),'-o',str(run/'objects'/(rel+'.olean')),str(run/'source'/(rel+'.lean'))]
def validate(run,receipt=None):
 run=Path(run).resolve();rr=read(receipt or run/'RESULT.json');need(rr['status']=='PASS_FRESH_SUPPLEMENT_ALL_SOURCES','complete supplement result required')
 need(rr['controller_sha256']==sha(__file__)==sha(run/'reproduce.executed.py'),'supplement controller identity')
 need(rr['primary_controller_sha256']==sha(I/'corrected/reproduce.py'),'primary controller pin')
 need(rr['resume_helper_sha256']==sha(HERE/'resume_dag.py'),'DAG resume helper pin')
 need(rr['BUILD_sha256']==sha(run/'BUILD.json')and rr['manifest_sha256']==sha(run/'SOURCE_CLOSURE.executed.json'),'supplement receipt binding');m=manifest_check(run/'SOURCE_CLOSURE.executed.json');ctx=P.context();maps,pr=primary_maps(rr['primary']['root']);need(pr==rr['primary'],'changed primary closure')
 reused=set()
 if rr.get('resume_source')is not None:
  prior,rs=validate_reuse(Path(rr['resume_source']['root']),m,ctx,maps);need(prior==rr['resume_source'],'interrupted origin evidence drift');reused={x['module']for x in rs}
 need(rr['same_campaign_completed_DAG_leaves_reused']==len(reused)and rr['fresh_compilations_this_attempt']==len(m['modules'])-len(reused),'transparent DAG reuse census')
 execution=Path(rr['execution_root']);need(execution.is_absolute(),'execution root');b=read(run/'BUILD.json');need(b['status']=='PASS'and len(b['modules'])==len(m['modules']),'complete supplemental build')
 for want,got in zip(m['modules'],b['modules']):
  mod=want['module'];rel=mod.replace('.','/');need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'compiler status')
  src=run/'source'/(rel+'.lean');obj=run/'objects'/(rel+'.olean');need(src.is_file()and obj.is_file()and not src.is_symlink()and not obj.is_symlink(),'owned source/object required')
  need(sha(src)==want['sha256']==got['source_sha256']and sha(obj)==got['object_sha256'],'source/object drift')
  cmdroot=Path(rr['resume_source']['root'])if mod in reused else execution
  need(got['command']==command(ctx,cmdroot,mod,rr['per_job_memory_cap_bytes'],rr['Lean_threads']),'actual compiler command')
  for suffix in ['stdout','stderr']:need(sha(run/'logs'/(mod+'.'+suffix))==got[suffix+'_sha256'],'compiler log drift')
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(run/'logs'/(mod+'.stderr')).read_text());need(rss is not None and type(got['peak_RSS_KiB'])is int and got['peak_RSS_KiB']==int(rss[1]),'actual child RSS row');maps[mod]={'object':obj,'object_sha256':got['object_sha256']}
 for q in m['resources']:need(sha(run/'source'/q['relative_runtime_path'])==q['sha256'],'include source identity')
 log=(run/'logs/FinalSupplementAudit.stdout').read_text();rows=[json.loads(l.split('RH_SUPPLEMENT_THEOREM ',1)[1])for l in log.splitlines()if 'RH_SUPPLEMENT_THEOREM {'in l];match=re.findall(r'RH_SUPPLEMENT_AUDIT_PASS (\d+)',log)
 need(len(match)==1 and int(match[0])==len(rows)>0 and len({x['name']for x in rows})==len(rows),'complete theorem audit')
 for q in rows:need(set(q['axioms'])<=P.ALLOW and q['module']in m['owned_modules'],'supplement axiom audit')
 body=[json.loads(l.split('RH_SUPPLEMENT_BODY ',1)[1])for l in log.splitlines()if 'RH_SUPPLEMENT_BODY {'in l];need(sorted(x['theorem']for x in body)==m['final_roots'],'every final canonical proof/body/axiom audit')
 need([x['module']for x in rr['dependency_probes']]==m['roots'],'exact ordered dependency probes')
 for q in rr['dependency_probes']:
  expect=[ctx['compiler'],'--root='+str(execution/'source'),'--deps',str(execution/'source'/(q['module'].replace('.','/')+'.lean'))];need(q['command']==expect and type(q['returncode'])is int and q['returncode']==0,'dependency command')
  for suff in ['stdout','stderr']:need(sha(run/'dependencies'/q[suff])==q[suff+'_sha256'],'dependency log drift')
  for line in (run/'dependencies'/q['stdout']).read_text().splitlines():
   f=Path(line).resolve();f=run/f.relative_to(execution)if f.is_relative_to(execution)else f;f=f.resolve();generic=[Path(p).resolve()for p in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
   if any(f.is_relative_to(p)for p in generic):continue
   ids=[v for v in maps.values()if v['object'].resolve()==f];need(len(ids)==1 and sha(f)==ids[0]['object_sha256'],'foreign/drifted application object')
 need(rr['new_modules']==len(m['modules']) and rr['total_source_modules']==454+len(m['modules']) and rr['compiler_sha256']==ctx['compiler_sha256'],'complete source census/compiler')
 need(rr['TREE_RSS_sha256']==sha(run/'TREE_RSS.csv'),'aggregate RSS evidence');samples=(run/'TREE_RSS.csv').read_text().splitlines();need(samples[0]=='seconds,process_tree_RSS_bytes,process_count,owned_disk_bytes'and len(samples)>1,'RSS sampling')
 parsed=[l.split(',')for l in samples[1:]];need(all(len(x)==4 for x in parsed),'RSS sample schema');need(max(int(x[1])for x in parsed)==rr['sampled_peak_process_tree_RSS_bytes'],'actual aggregate peak')
 need(max(int(x[3])for x in parsed)==rr['sampled_peak_owned_disk_bytes']<=300*(1<<30),'sampled scratch cap/metric')
 need(rr['peak_individual_child_RSS_KiB']==max(x['peak_RSS_KiB']for x in b['modules']),'individual child maximum')
 need(rr['observed_process_OOM_events']==0 and type(rr['observed_process_OOM_events'])is int,'OOM acceptance')
 need(rr['historical_application_cache_used']is False and rr['DEV_application_objects_used']is False and rr['whole_pipeline_source_first_PV']is False and rr['official_Comparator_receipt']is False,'trust labels')
 return rr
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--primary',type=Path);ap.add_argument('--out',type=Path);ap.add_argument('--verify',type=Path);ap.add_argument('--resume',type=Path);ap.add_argument('--jobs',type=int,default=8);ap.add_argument('--memory-gib',type=int,default=64);ap.add_argument('--threads',type=int,default=2);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 if a.verify:need(a.out is None and a.primary is None and a.resume is None,'verify arguments');r=validate(a.verify);print(json.dumps({'status':'PASS_SUPPLEMENT_READBACK','modules':r['new_modules'],'optimization':sys.flags.optimize}));return
 need(a.primary is not None and a.out is not None,'--primary and --out required');need(1<=a.jobs<=16 and 1<=a.memory_gib<=300 and 1<=a.threads<=16,'resource policy');out=a.out.resolve();need(not out.exists(),'fresh output required');ctx=P.context();m=manifest_check(HERE/'capture/SOURCE_CLOSURE.json');maps,primary=primary_maps(a.primary);memory=a.memory_gib<<30
 if a.check:print('PASS_SOURCE_ONLY_SUPPLEMENT_PREFLIGHT');return
 avail=available();reserve=512<<30;need(avail>=reserve+a.jobs*memory,'parallel memory caps exceed available RAM and512GiB host reserve');need(shutil.disk_usage(out.parent).free>=10<<30,'independent free disk admission');out.mkdir(parents=True)
 admission={'MemAvailable_bytes':avail,'host_reserve_bytes':reserve,'per_job_address_space_cap_bytes':memory,'max_parallel_jobs':a.jobs,'free_disk_bytes':shutil.disk_usage(out.parent).free,'scratch_cap_bytes':300<<30};save(out/'RESOURCE_ADMISSION.json',admission)
 for d in ['source','objects','union','logs','dependencies']:(out/d).mkdir()
 (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes());(out/'SOURCE_CLOSURE.executed.json').write_bytes((HERE/'capture/SOURCE_CLOSURE.json').read_bytes())
 for mod,q in maps.items():
  p=out/'union'/(mod.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(q['object'])
 for q in m['resources']:
  p=out/'source'/q['relative_runtime_path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/q['path']).read_bytes())
 for q in m['modules']:
  p=out/'source'/(q['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/q['path']).read_bytes());(out/'objects'/q['module'].replace('.','/')).parent.mkdir(parents=True,exist_ok=True)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'union'),*ctx['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1';start=time.monotonic();records={};probes=[];resume_source=None
 if a.resume:
  need(a.memory_gib==64 and a.threads==2,'resume preserves original64GiB/2thread per-job policy');resume_source,rs=validate_reuse(a.resume.resolve(),m,ctx,maps);records=copy_reuse(a.resume.resolve(),out,rs,maps);save(out/'RESUME.json',{'status':'ADMITTED_SAME_CAMPAIGN_SOURCE_FRESH_COMPLETED_DAG_ONLY','origin':resume_source})
 stats={'peak_RSS_bytes':0,'peak_disk_bytes':0,'last_disk':0,'samples':0};stop=threading.Event();mon=threading.Thread(target=monitor,args=(out,stop,stats),daemon=True);mon.start()
 def compile_one(q):
  mod=q['module'];cmd=command(ctx,out,mod,memory,a.threads);t=time.monotonic();so=out/'logs'/(mod+'.stdout');se=out/'logs'/(mod+'.stderr')
  with so.open('w')as fo,se.open('w')as fe:cp=subprocess.run(cmd,cwd=out/'source',env=env,text=True,stdout=fo,stderr=fe)
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',se.read_text());need(rss is not None,'child RSS missing:'+mod);row={'module':mod,'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(out/'source'/(mod.replace('.','/')+'.lean')),'stdout_sha256':sha(so),'stderr_sha256':sha(se),'peak_RSS_KiB':int(rss[1])}
  if cp.returncode==0:row['object_sha256']=sha(out/'objects'/(mod.replace('.','/')+'.olean'))
  return row
 try:
  pending=[x for x in m['modules']if x['module']not in records];running={};done=set(maps)
  with cf.ThreadPoolExecutor(max_workers=a.jobs)as pool:
   while pending or running:
    for q in pending[:]:
     if len(running)>=a.jobs:break
     if set(q['application_imports'])<=done:running[pool.submit(compile_one,q)]=q;pending.remove(q)
    need(bool(running),'unresolved DAG dependencies')
    ready,_=cf.wait(running,return_when=cf.FIRST_COMPLETED)
    for future in ready:
     q=running.pop(future);row=future.result();need('monitor_error'not in stats,'resource sampler failed');need(disk(out)<=300*(1<<30) and stats['peak_disk_bytes']<=300*(1<<30),'experiment-owned scratch cap');mod=q['module'];records[mod]=row;save(out/'BUILD.json',{'status':'RUNNING'if row['returncode']==0 else'FAIL','modules':[records[x['module']]for x in m['modules']if x['module']in records]});need(row['returncode']==0,'supplement compiler failed:'+mod);need(row['source_sha256']==q['sha256'],'source drift during compile')
     obj=out/'objects'/(mod.replace('.','/')+'.olean');link=out/'union'/(mod.replace('.','/')+'.olean');link.parent.mkdir(parents=True,exist_ok=True);need(not link.exists(),'namespace collision');link.symlink_to(obj);done.add(mod);print(len(records),len(m['modules']),mod,round(row['seconds'],2),flush=True)
  for mod in m['roots']:
   cmd=[ctx['compiler'],'--root='+str(out/'source'),'--deps',str(out/'source'/(mod.replace('.','/')+'.lean'))];cp=subprocess.run(cmd,cwd=out/'source',env=env,capture_output=True,text=True);so=out/'dependencies'/(mod+'.stdout');se=out/'dependencies'/(mod+'.stderr');so.write_text(cp.stdout);se.write_text(cp.stderr);need(cp.returncode==0,'dependency probe failed');probes.append({'module':mod,'command':cmd,'returncode':cp.returncode,'stdout':so.name,'stderr':se.name,'stdout_sha256':sha(so),'stderr_sha256':sha(se)})
  stop.set();mon.join();need('monitor_error'not in stats and stats['samples']>0,'complete resource sampling');need(disk(out)<=300*(1<<30) and stats['peak_disk_bytes']<=300*(1<<30),'final scratch cap');ordered=[records[x['module']]for x in m['modules']];save(out/'BUILD.json',{'status':'PASS','modules':ordered});rr={'schema':'RH_OCTIC_SUPPLEMENT_REPLAY_V1','status':'PASS_FRESH_SUPPLEMENT_ALL_SOURCES','execution_root':str(out),'primary':primary,'resume_source':resume_source,'resume_helper_sha256':sha(HERE/'resume_dag.py'),'same_campaign_completed_DAG_leaves_reused':resume_source['completed_count']if resume_source else 0,'fresh_compilations_this_attempt':len(ordered)-(resume_source['completed_count']if resume_source else 0),'manifest_sha256':sha(HERE/'capture/SOURCE_CLOSURE.json'),'controller_sha256':sha(__file__),'primary_controller_sha256':sha(I/'corrected/reproduce.py'),'BUILD_sha256':sha(out/'BUILD.json'),'compiler_sha256':ctx['compiler_sha256'],'new_modules':len(ordered),'total_source_modules':454+len(ordered),'seconds':time.monotonic()-start,'Lean_threads':a.threads,'per_job_memory_cap_bytes':memory,'max_parallel_jobs':a.jobs,'peak_individual_child_RSS_KiB':max(x['peak_RSS_KiB']for x in ordered),'sampled_peak_process_tree_RSS_bytes':stats['peak_RSS_bytes'],'aggregate_RAM_measurement':'Whole controller descendant tree VmRSS sampled every0.5s; includes concurrent time/Lean subprocesses; not sum of individual high-water marks','sampled_peak_owned_disk_bytes':stats['peak_disk_bytes'],'owned_disk_before_result_bytes':disk(out),'disk_measurement':'Disk sampled every5s and cap checked at compiler completions/final; not an intra-compiler exact high-water mark','TREE_RSS_sha256':sha(out/'TREE_RSS.csv'),'resource_admission':admission,'observed_process_OOM_events':0,'OOM_evidence':'All admitted compilation/probe processes returned0; no assertion about unattributed host global counters','dependency_probes':probes,'historical_application_cache_used':False,'DEV_application_objects_used':False,'whole_pipeline_source_first_PV':False,'official_Comparator_receipt':False,'numerical_verification':'Ordinary Lean kernel rational/interval certificate proofs, no native numerical leaves; not source-first PV','trust':'Explicit RH/Green/Nicolas/BPT (and finiteGoldbach when used) inputs remain. Existing C rendered-source identity relies on its renderer/model interpretation; independent parser soundness not established here. Pinned compiler/runtime/OS/hardware contracts remain.','python_optimization':sys.flags.optimize};candidate=out/'CANDIDATE.json';save(candidate,rr);validate(out,candidate);os.replace(candidate,out/'RESULT.json');print(rr['status'])
 except BaseException as ex:
  stop.set();mon.join();save(out/'FAILURE.json',{'error':str(ex),'completed_modules':len(records),'seconds':time.monotonic()-start});raise
if __name__=='__main__':main()
