#!/usr/bin/env python3
"""Fresh source replay above the exact 261+55+24 foundation.

From clean: --out DIR rebuilds all three foundation routes, new sources and C
executions. --basis DIR may reuse only a fully hash-checked current-campaign
foundation. --verify DIR performs readback without compiling or changing DIR.
No acceptance check uses assert or __debug__.
"""
from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,math,os,re,resource,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent;S=HERE.parent;R=S.parents[1]
ALLOW={'propext','Classical.choice','Quot.sound'}
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(s):
  v=float(s);need(math.isfinite(v),'nonfinite JSON number');return v
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON constant')))
def save(p,d):
 q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'pending receipt collision');q.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def load(name,path):
 sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
def context():
 ref=read(R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json');f=Path(os.environ.get('IEANTN_GENERIC_CONTEXT',R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'));ctx=read(f)
 need(ctx['compiler_sha256']==ref['compiler_sha256']==sha(ctx['compiler']),'compiler identity')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in ref['generic_dependencies']],'generic source pins')
 need(ctx['generic_libraries']==[d['library']for d in ctx['generic_dependencies']if d['library_present']],'generic-only libraries')
 for d in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic revision')
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'generic tracked source drift')
 return ctx

def validate_foundation(root):
 root=Path(root).resolve();pi=root/'pi';spectral=root/'spectral';canonical=root/'canonical'
 u=load('old_complete_integration',R/'Solutions/RHLimit.v1/scripts/reproduce_integration.py');bm,br=u.u.validate_basis(pi);sm,sr=u.validate_spectral(pi,spectral)
 refs=[(pi,'pi','scripts/reproduce_pi_complete.py'),(spectral,'spectral','spectral/reproduce_cold_append.py'),(canonical,'integration','scripts/reproduce_integration.py')]
 result=read(canonical/'RESULT.json');build=read(canonical/'BUILD.json');manifest=read(R/'Solutions/RHLimit.v1/integration/SOURCE_CLOSURE.json')
 need(result['status']=='PASS_COMPLETE_340_SOURCE_NETWORK_EVOLUTION_CONSUMERS','complete canonical340 required')
 need(result['basis_RESULT_sha256']==sha(pi/'RESULT.json')and result['spectral_RESULT_sha256']==sha(spectral/'RESULT.json'),'canonical basis association')
 need(result['BUILD_sha256']==sha(canonical/'BUILD.json')and build['status']=='PASS','canonical build binding')
 need(result['source_manifest_sha256']==sha(R/'Solutions/RHLimit.v1/integration/SOURCE_CLOSURE.json')==sha(canonical/'SOURCE_CLOSURE.executed.json'),'canonical manifest binding')
 need(len(build['modules'])==len(manifest['modules'])==24,'all24 canonical sources')
 for want,got in zip(manifest['modules'],build['modules']):
  mod=want['module'];rel=mod.replace('.','/');need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'canonical compiler status')
  need(sha(R/want['path'])==want['sha256']==got['source_sha256']==sha(canonical/'source'/(rel+'.lean')),'canonical source')
  if 'original_path'in want:need(sha(R/want['original_path'])==want['sha256'],'current old canonical source')
  need(sha(canonical/'objects'/(rel+'.olean'))==got['object_sha256'],'canonical object')
  for suf,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256')]:need(sha(canonical/'logs'/(mod+'.'+suf))==got[key],'canonical log')
  u.audit((canonical/'logs'/(mod+'.stdout')).read_text())
 for run,part,controller in refs:
  rr=read(run/'RESULT.json');need(sha(run/'reproduce.executed.py')==rr['controller_sha256']==sha(R/'Solutions/RHLimit.v1'/controller),'foundation actual controller')
  need(sha(run/'SOURCE_CLOSURE.executed.json')==sha(R/'Solutions/RHLimit.v1'/part/'SOURCE_CLOSURE.json'),'foundation actual manifest')
 # Complete coefficient executable/source/model/stdout association, including logs.
 cdir=spectral/'C-execution';c=read(cdir/'RESULT.json')
 for path,key in [('rh_coeff.c','C_source_sha256'),('driver.c','driver_sha256'),('rh_coeff','binary_sha256'),('outputs.txt','outputs_sha256')]:need(sha(cdir/path)==c[key],'coefficient C artifact:'+path)
 need(c['controller_sha256']==sha(R/'Solutions/RHLimit.v1/spectral/reproduce_coeff_execution.py'),'coefficient controller')
 need(br['prebuilt_application_objects_used']is False and br['prebuilt_LeanCert_objects_used']is False and sr['historical_application_or_LeanCert_objects_used']is False and result['historical_application_cache_used']is False,'historical application cache')
 # Current-campaign admission is explicit; no old publication bank can pass merely by its path.
 need(Path(root/'PIPELINE.json').is_file(),'campaign foundation pipeline receipt missing')
 pipeline=read(root/'PIPELINE.json');need(len(pipeline.get('routes',[]))==3,'all three campaign routes required')
 for route in pipeline['routes']:need(type(route.get('returncode'))is int and route['returncode']==0,'incomplete campaign route')
 maps={}
 for run,m in [(pi,bm),(spectral,sm),(canonical,manifest)]:
  rows=read(run/'BUILD.json')['modules']
  for want,got in zip(m['modules'],rows):
   need(want['module']not in maps,'foundation namespace collision');maps[want['module']]={'source':run/'source'/(want['module'].replace('.','/')+'.lean'),'object':run/'objects'/(want['module'].replace('.','/')+'.olean'),'object_sha256':got['object_sha256']}
 need(len(maps)==340,'exact340 namespace')
 return maps,{'root':str(root),'pi_RESULT_sha256':sha(pi/'RESULT.json'),'spectral_RESULT_sha256':sha(spectral/'RESULT.json'),'canonical_RESULT_sha256':sha(canonical/'RESULT.json'),'PIPELINE_sha256':sha(root/'PIPELINE.json')}

def manifest_check(path):
 need(sha(path)==sha(HERE/'capture/SOURCE_CLOSURE.json'),'not the registered immutable primary capture');m=read(path);need(m['schema']=='RH_OCTIC_NEW_SOURCE_CLOSURE_V1','manifest schema');need(m['selector_sha256']==sha(HERE/'prepare_capture.py'),'source selector identity');need(m['scope_policy_sha256']==sha(HERE/'PRIMARY_SCOPE_POLICY.json'),'primary scope policy identity');done=set()
 for b in m['baseline_manifests']:
  need(sha(R/b['path'])==b['sha256'],'foundation manifest source drift');done.update(x['module']for x in read(R/b['path'])['modules'])
 need(len(done)==340,'exact foundation340')
 for row in m['modules']:
  need(row['module']not in done,'duplicate module');need(set(row['application_imports'])<=done,'incomplete/order source closure')
  f=Path(row['path']);f=f if f.is_absolute()else R/f;need(f.is_file()and sha(f)==row['sha256'],'captured source drift:'+row['module'])
  if row['original_path']is not None:need(sha(R/row['original_path'])==row['sha256'],'working source drift:'+row['module'])
  need('.Challenge'not in row['module'],'admitted Challenge source');done.add(row['module'])
 for row in m['resources']:
  need(sha(R/row['path'])==row['sha256'],'include payload source drift');need(not Path(row['relative_runtime_path']).is_absolute()and'..'not in Path(row['relative_runtime_path']).parts,'include runtime path scope')
 return m

def disk(p):return sum(f.stat().st_size for f in p.rglob('*')if f.is_file()and not f.is_symlink())
def run_stage(out,name,cmd,env):
 t=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,text=True,capture_output=True);(out/(name+'.stdout')).write_text(cp.stdout);(out/(name+'.stderr')).write_text(cp.stderr);need(cp.returncode==0,'stage failed:'+name);return {'name':name,'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,'stdout_sha256':sha(out/(name+'.stdout')),'stderr_sha256':sha(out/(name+'.stderr'))}

def validate(run,receipt_path=None):
 run=Path(run).resolve();rr=read(receipt_path if receipt_path is not None else run/'RESULT.json');need(rr['status']=='PASS_FRESH_FOUNDATION_AND_ALL_NEW_SOURCES','completed fresh source replay required')
 need(rr['controller_sha256']==sha(__file__)==sha(run/'reproduce.executed.py'),'new controller identity')
 need(sha(run/'SOURCE_CLOSURE.executed.json')==rr['manifest_sha256'],'new manifest binding');m=manifest_check(run/'SOURCE_CLOSURE.executed.json');execution_root=Path(rr['execution_root']);need(execution_root.is_absolute(),'execution root');ctx=context();maps,foundation=validate_foundation(rr['foundation']['root']);need(foundation==rr['foundation'],'foundation changed')
 for item in maps.values():
  if item['object'].resolve().is_relative_to(execution_root):
   item['object']=run/item['object'].resolve().relative_to(execution_root)
   need(sha(item['object'])==item['object_sha256'],'relocated foundation object drift')
 need(sha(run/'BUILD.json')==rr['BUILD_sha256'],'new build binding');b=read(run/'BUILD.json');need(b['status']=='PASS'and len(b['modules'])==len(m['modules']),'all new modules')
 for want,got in zip(m['modules'],b['modules']):
  mod=want['module'];rel=mod.replace('.','/');need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'new compiler status')
  f=run/'source'/(rel+'.lean');obj=run/'objects'/(rel+'.olean');need(f.is_file()and not f.is_symlink()and obj.is_file()and not obj.is_symlink(),'source/object must be owned regular file')
  need(sha(f)==want['sha256']==got['source_sha256']and sha(obj)==got['object_sha256'],'new source/object identity')
  for suf,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256')]:need(sha(run/'logs'/(mod+'.'+suf))==got[key],'new log identity')
  expected=['/usr/bin/time','-v',ctx['compiler'],'--root='+str(execution_root/'source'),'-j'+str(rr['Lean_threads']),'-o',str(execution_root/'objects'/(rel+'.olean')),str(execution_root/'source'/(rel+'.lean'))];need(got['command']==expected,'exact new execution command')
  maps[mod]={'object':obj,'object_sha256':got['object_sha256']}
 for row in m['resources']:need(sha(run/'source'/row['relative_runtime_path'])==row['sha256'],'executed include identity')
 a=(run/'logs/FinalSourceAudit.stdout').read_text();ar=[read_json_line(x.split('RH_NEW_THEOREM ',1)[1])for x in a.splitlines()if'RH_NEW_THEOREM {'in x]
 match=re.findall(r'RH_NEW_THEOREM_AUDIT_PASS (\d+)',a);need(len(match)==1 and int(match[0])==len(ar)>0,'complete actual theorem audit')
 need(len({x['name']for x in ar})==len(ar),'duplicate theorem audit');need(set(m['final_roots'])<={x['name']for x in ar},'missing canonical root proof audit')
 for row in ar:need(set(row['axioms'])<=ALLOW and row['module']in m['owned_modules'],'unaccepted theorem axiom/provenance')
 need([p['module']for p in rr['dependency_probes']]==m['roots'],'complete ordered dependency probes')
 for probe in rr['dependency_probes']:
  expected=[ctx['compiler'],'--root='+str(execution_root/'source'),'--deps',str(execution_root/'source'/(probe['module'].replace('.','/')+'.lean'))];need(probe['command']==expected,'exact dependency probe command')
  need(sha(run/'dependencies'/probe['stdout'])==probe['stdout_sha256']and sha(run/'dependencies'/probe['stderr'])==probe['stderr_sha256'],'dependency probe log')
  need(probe['returncode']==0,'dependency command failed')
  for path in (run/'dependencies'/probe['stdout']).read_text().splitlines():
   f=Path(path.strip()).resolve();f=run/f.relative_to(execution_root)if f.is_relative_to(execution_root)else f;f=f.resolve();allowed=[Path(x).resolve()for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
   if any(f.is_relative_to(x)for x in allowed):continue
   identity=[v for v in maps.values()if v['object'].resolve()==f];need(len(identity)==1 and sha(f)==identity[0]['object_sha256'],'foreign/drifted application dependency')
 for row in rr['C_artifacts']:
  path=(run/row['path']).resolve();need(path.is_relative_to(run),'C artifact path escapes run');need(sha(path)==row['sha256'],'C build/run/controller/log artifact drift')
 for stage in rr['stages']:
  need(type(stage['returncode'])is int and stage['returncode']==0,'stage status')
  for suf in ['stdout','stderr']:need(sha(run/(stage['name']+'.'+suf))==stage[suf+'_sha256'],'stage log')
 native=read(run/'C-log127/NATIVE.json');cr=read(run/'C-ram/RECEIPT.json')
 need(native['status']=='NATIVE_SOURCE_BUILD_RUN_COMPLETE_FORMAL_ACCEPTANCE_SEPARATE'and[x['n']for x in native['rows']]==list(range(2,129)),'all127 actual C rows')
 need(sha(run/'C-log127/CLogNativeRows.lean')==sha(R/'Solutions/RHContinuation.v1/parabolic/CLogNativeRows.lean'),'actual C rows/formal source')
 need(cr['status']=='PASS_ACTUAL_C_OUTPUT_ASSOCIATION'and type(cr['rows'])is int and cr['rows']==25 and cr['new_prime_count_coverage_proved']is False,'high-log/coefficient C status')
 need(cr['script_sha256']==sha(S/'ramanujan/reproduce_c_inputs.py')and cr['source_record_sha256']==sha(S/'ramanujan/C_LOG_EXECUTION.json')and cr['source_audit_sha256']==sha(S/'ramanujan/SOURCE_PROGRAM_AUDIT.json'),'C source controller/input pins')
 for file,key in [('verified_finite_log.c','source_sha256'),('rh_coeff.c','coefficient_source_sha256'),('harness.c','harness_sha256'),('run','executable_sha256'),('stdout','stdout_sha256')]:need(sha(run/'C-ram'/file)==cr[key],'C actual artifact association')
 need(native['C_source_sha256']==cr['source_sha256']==sha(R/'Solutions/RamanujanSourcePV.v1/c/verified_finite_log.c'),'same actual logarithm source')
 need(rr['compiler_sha256']==ctx['compiler_sha256']and rr['new_modules']==len(m['modules'])and rr['total_source_modules']==340+len(m['modules']),'run census/compiler')
 need(type(rr['observed_process_OOM_events'])is int and rr['observed_process_OOM_events']==0,'accepted process OOM event claim')
 need(rr['historical_application_cache_used']is False and rr['official_Comparator_receipt']is False and rr['whole_pipeline_source_first_PV']is False,'trust label changed')
 return rr

def read_json_line(s):
 v=json.loads(s);need(type(v)is dict and set(v)=={'name','module','axioms'},'theorem audit schema');return v

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path);p.add_argument('--basis',type=Path);p.add_argument('--manifest',type=Path,default=HERE/'capture/SOURCE_CLOSURE.json');p.add_argument('--verify',type=Path);p.add_argument('--check',action='store_true');p.add_argument('--memory-gib',type=int,default=128);p.add_argument('--threads',type=int,default=4);a=p.parse_args()
 if a.verify:
  need(a.out is None and a.basis is None and not a.check,'verify mode arguments');r=validate(a.verify);print(json.dumps({'status':'PASS_COMPLETE_READBACK','new_modules':r['new_modules'],'optimization':sys.flags.optimize}));return
 need(a.out is not None,'--out required');out=a.out.resolve();need(not out.exists(),'fresh output required');need(1<=a.memory_gib<=300 and 1<=a.threads<=32,'resource policy');ctx=context();m=manifest_check(a.manifest);basis=a.basis.resolve()if a.basis else out/'foundation'
 if a.basis:maps,fr=validate_foundation(basis)
 if a.check:print('PASS_SOURCE_MANIFEST_CONTEXT_AND_EXISTING_BASIS_PREFLIGHT');return
 available=next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:'));need(available>=(512+a.memory_gib)*(1<<30),'host reserve')
 disk_free=shutil.disk_usage(out.parent).free;need(disk_free>=10*(1<<30),'independent free disk admission');out.mkdir(parents=True);admission={'MemAvailable_bytes':available,'disk_free_bytes':disk_free,'memory_cap_bytes':a.memory_gib<<30,'scratch_cap_bytes':300<<30,'host_RAM_reserve_bytes':512<<30};save(out/'RESOURCE_ADMISSION.json',admission);start=time.monotonic();env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';stages=[]
 if not a.basis:
  basis.mkdir();routes=[('pi',R/'Solutions/RHLimit.v1/scripts/reproduce_pi_complete.py',['--out',str(basis/'pi')]),('spectral',R/'Solutions/RHLimit.v1/spectral/reproduce_cold_append.py',['--basis',str(basis/'pi'),'--out',str(basis/'spectral')]),('canonical',R/'Solutions/RHLimit.v1/scripts/reproduce_integration.py',['--basis',str(basis/'pi'),'--spectral',str(basis/'spectral'),'--out',str(basis/'canonical')])];pr=[]
  for name,script,args in routes:
   rec=run_stage(out,'foundation-'+name,[sys.executable,str(script),*args],env);stages.append(rec);pr.append({'route':name,'command':rec['command'],'returncode':0,'wall_seconds':rec['seconds'],'script_sha256':sha(script)});save(basis/'PIPELINE.json',{'status':'PASS'if len(pr)==3 else'RUNNING','routes':pr,'campaign':'RHOcticPush.v1'})
  maps,fr=validate_foundation(basis)
 src=out/'source';obj=out/'objects';union=out/'union';logs=out/'logs';deps=out/'dependencies'
 for d in [src,obj,union,logs,deps]:d.mkdir()
 for mod,row in maps.items():
  q=union/(mod.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(row['object'])
 (out/'SOURCE_CLOSURE.executed.json').write_bytes(a.manifest.read_bytes());(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
 for row in m['resources']:
  q=src/row['relative_runtime_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((R/row['path']).read_bytes())
 env['LEAN_PATH']=':'.join([str(union),*ctx['generic_libraries']]);records=[];probes=[]
 try:
  for want in m['modules']:
   mod=want['module'];rel=mod.replace('.','/');f=src/(rel+'.lean');f.parent.mkdir(parents=True,exist_ok=True);origin=Path(want['path']);origin=origin if origin.is_absolute()else R/origin;f.write_bytes(origin.read_bytes());o=obj/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
   cmd=['/usr/bin/time','-v',ctx['compiler'],'--root='+str(src),'-j'+str(a.threads),'-o',str(o),str(f)];t=time.monotonic();cp=subprocess.run(cmd,cwd=src,env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(a.memory_gib<<30,a.memory_gib<<30)))
   so=logs/(mod+'.stdout');se=logs/(mod+'.stderr');so.write_text(cp.stdout);se.write_text(cp.stderr);rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',cp.stderr);need(rss is not None,'RSS absent')
   row={'module':mod,'source_sha256':sha(f),'returncode':cp.returncode,'seconds':time.monotonic()-t,'command':cmd,'peak_RSS_KiB':int(rss[1]),'stdout_sha256':sha(so),'stderr_sha256':sha(se),'owned_disk_after_bytes':disk(out)}
   if cp.returncode==0:row['object_sha256']=sha(o)
   need(row['owned_disk_after_bytes']<=300*(1<<30),'experiment-owned scratch cap');records.append(row);save(out/'BUILD.json',{'status':'RUNNING'if cp.returncode==0 else'FAIL','modules':records});need(cp.returncode==0,'new source compile failed:'+mod);need(sha(f)==want['sha256'],'new source drift during replay')
   q=union/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);need(not q.exists(),'new namespace collision');q.symlink_to(o);maps[mod]={'object':o,'object_sha256':sha(o)};print(len(records),len(m['modules']),mod,round(row['seconds'],2),flush=True)
  for mod in m['roots']:
   cmd=[ctx['compiler'],'--root='+str(src),'--deps',str(src/(mod.replace('.','/')+'.lean'))];cp=subprocess.run(cmd,cwd=src,env=env,text=True,capture_output=True);so=deps/(mod+'.stdout');se=deps/(mod+'.stderr');so.write_text(cp.stdout);se.write_text(cp.stderr);need(cp.returncode==0,'new dependency probe:'+mod);probes.append({'module':mod,'command':cmd,'returncode':cp.returncode,'stdout':so.name,'stderr':se.name,'stdout_sha256':sha(so),'stderr_sha256':sha(se)})
  env.pop('LEAN_PATH',None)
  stages.append(run_stage(out,'C-log127',[sys.executable,str(R/'Solutions/RHContinuation.v1/parabolic/native_log_workload.py'),'--out',str(out/'C-log127')],env))
  stages.append(run_stage(out,'C-ram',[sys.executable,str(S/'ramanujan/reproduce_c_inputs.py'),'--out',str(out/'C-ram')],env))
  native=read(out/'C-log127/NATIVE.json');need(native['status']=='NATIVE_SOURCE_BUILD_RUN_COMPLETE_FORMAL_ACCEPTANCE_SEPARATE'and [x['n']for x in native['rows']]==list(range(2,129)),'all127 actual C inputs');need(sha(out/'C-log127/CLogNativeRows.lean')==sha(R/'Solutions/RHContinuation.v1/parabolic/CLogNativeRows.lean'),'C outputs differ from formal rows')
  cr=read(out/'C-ram/RECEIPT.json');need(cr['status']=='PASS_ACTUAL_C_OUTPUT_ASSOCIATION'and cr['rows']==25 and cr['new_prime_count_coverage_proved']is False,'actual4log21coeff C join')
  cart=[{'path':str(f.relative_to(out)),'sha256':sha(f)}for dr in ['C-log127','C-ram']for f in sorted((out/dr).rglob('*'))if f.is_file()and not f.is_symlink()]
  save(out/'BUILD.json',{'status':'PASS','modules':records});rr={'schema':'RH_OCTIC_FRESH_SOURCE_REPLAY_V1','status':'PASS_FRESH_FOUNDATION_AND_ALL_NEW_SOURCES','execution_root':str(out),'foundation':fr,'manifest_sha256':sha(a.manifest),'controller_sha256':sha(__file__),'BUILD_sha256':sha(out/'BUILD.json'),'compiler_sha256':ctx['compiler_sha256'],'resource_admission':admission,'new_modules':len(records),'total_source_modules':340+len(records),'seconds':time.monotonic()-start,'Lean_threads':a.threads,'memory_cap_bytes':a.memory_gib<<30,'peak_child_RSS_KiB':max(x['peak_RSS_KiB']for x in records),'sampled_peak_owned_disk_bytes':max(x['owned_disk_after_bytes']for x in records),'disk_measurement':'sampled after each module; not an intra-compiler high-water mark','observed_process_OOM_events':0,'OOM_evidence':'all admitted compiler processes returned0; host global OOM counters not attributed','dependency_probes':probes,'C_artifacts':cart,'stages':stages,'historical_application_cache_used':False,'official_Comparator_receipt':False,'whole_pipeline_source_first_PV':False,'trust':'Actual restricted C source/model proofs plus unchanged C source-build-run joins; Lean kernel arithmetic is not PV. Compiler/runtime/OS/API/hardware contracts and explicit analytic/literature/RH inputs remain.','python_optimization':sys.flags.optimize};candidate=out/'CANDIDATE.json';save(candidate,rr);validate(out,candidate);os.replace(candidate,out/'RESULT.json');print(rr['status'])
 except BaseException as ex:save(out/'FAILURE.json',{'error':str(ex),'seconds':time.monotonic()-start,'completed_modules':len(records)});raise
if __name__=='__main__':main()
