#!/usr/bin/env python3
"""Bounded two-worker kernel scheduling scout; no new source-PV claim."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,math,os,re,shutil,signal,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
AXIOMS={'propext','Classical.choice','Quot.sound'}
DISK_CACHE={}
D=Path('/data/ivy-ramanujan-source-pv-20261119')
def need(condition,message):
 if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def strict_text(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate key');d[k]=v
  return d
 def finite(x):
  v=float(x);need(math.isfinite(v),'nonfinite');return v
 def bad(x):raise ValueError('invalid JSON constant '+x)
 return json.loads(text,object_pairs_hook=pairs,parse_float=finite,parse_constant=bad)
def strict(path):return strict_text(Path(path).read_text())
def atomic(path,value):
 path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');tmp.replace(path)
def available():return int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024
def guard(reserved):
 ram=available();disk=shutil.disk_usage('/data').free
 if time.monotonic()-DISK_CACHE.get('at',-100)>5:
  allocated=int(subprocess.check_output(['/usr/bin/du','-sx','-B1',str(D)],text=True).split()[0])
  DISK_CACHE.update(at=time.monotonic(),allocated=allocated)
 need(DISK_CACHE['allocated']<=300<<30,'owned project scratch exceeds300GiB')
 need(ram>=2**40 and ram>=(512<<30)+reserved,'actual RAM/reserve unavailable')
 need(disk>=2**40,'separate free disk unavailable')
 return dict(memavailable_bytes=ram,separate_free_disk_bytes=disk,reserved_bytes=reserved,allocated_bytes=DISK_CACHE['allocated'],allocated_root=str(D),allocation_sample_age_seconds=time.monotonic()-DISK_CACHE['at'])
def read_record(receipt,expected_source=None,reports_required=True):
 r=strict(receipt);need(r['status']=='COMPILED'and r['returncode']==0,'module did not compile')
 p=Path(r['source']);need(sha(p)==r['source_sha256']and p.read_bytes()==(Path(receipt).parent/'source.lean').read_bytes(),'source snapshot mismatch')
 if expected_source:need(r['source_sha256']==expected_source,'manifest source mismatch')
 for field,name in [('stdout_sha256','stdout'),('stderr_sha256','stderr'),('rusage_sha256','rusage.txt')]:need(sha(Path(receipt).parent/name)==r[field],'payload hash mismatch')
 text=(Path(receipt).parent/'stdout').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if reports_required:need(reports,'mandatory axiom report absent')
 for decl,ax in reports:need(set(x.strip()for x in ax.split(',')if x.strip())<=AXIOMS,'unexpected axiom '+decl)
 usage=(Path(receipt).parent/'rusage.txt').read_text();peak=re.search(r'Maximum resident set size \(kbytes\): (\d+)',usage);need(peak is not None,'RSS missing')
 return dict(module=r['module'],receipt=str(receipt),receipt_sha256=sha(receipt),source_sha256=r['source_sha256'],elapsed_seconds=r['elapsed_seconds'],peak_worker_rss_bytes=int(peak.group(1))*1024,memory_as_bytes=r['memory_limit_bytes'],affinity=r['affinity'],axiom_reports=reports,kind=None)
def check_value(a):
 need(a['status']=='COMPLETE_KERNEL_MASK_CHUNKING_SCOUT_NOT_PV','not complete')
 need(sha(__file__)==a['runner_sha256'],'runner changed')
 need(sha(a['manifest'])==a['manifest_sha256'],'manifest changed')
 need(sha(S/'scripts/compile_lean.py')==a['compile_helper_sha256'],'compile helper changed')
 need(sha(S/'RamanujanPV/PackedMaskChunks.lean')==a['generic_math_sha256'],'generic math changed')
 need(sha(S/'BUILD_CONTEXT.json')==a['context_sha256'],'context changed')
 manifest=strict(a['manifest']);prefix='RamanujanPV.PackedMaskChunkControl'if manifest['control_only']else'RamanujanPV.PackedMaskChunkPilot'
 expected={x['module']for x in manifest['records']}|{prefix+'.IndependentTypeAudit'}
 actual=[x['module']for x in a['records']]
 need(len(actual)==len(set(actual))and set(actual)==expected,'exact proof/data/audit census required')
 need(set(a['cases'])=={str(k)for k in manifest['partitions']},'exact completed case census required')
 for k in manifest['partitions']:need(a['cases'][str(k)]['partitions']==k,'case identity')
 need(len(a['resource_samples'])==len(a['records']),'dispatch resource sample census')
 for sample in a['resource_samples']:
  need(sample['reserved_bytes']==96<<30,'exact two-worker reservation bound')
  need(sample['memavailable_bytes']>=2**40 and sample['memavailable_bytes']>=(512<<30)+sample['reserved_bytes'],'RAM sample invalid')
  need(sample['separate_free_disk_bytes']>=2**40 and sample['allocated_bytes']<=300<<30 and sample['allocation_sample_age_seconds']<=6,'disk sample invalid')
 for row in a['records']:
  need(row['memory_as_bytes']==48<<30 and len(row['affinity'])==1 and row['affinity'][0]in[32,33],'actual child resource policy')
  reread=read_record(row['receipt'],row['source_sha256'],not row['module'].endswith('.Data'));need(reread['receipt_sha256']==row['receipt_sha256'],'receipt changed')
  need(sha(row['object_snapshot'])==row['object_sha256']==strict(row['receipt'])['object_sha256'],'object snapshot/receipt link changed')
 return a
def check(result):return check_value(strict(result))

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path);p.add_argument('--out',type=Path);p.add_argument('--cpus',default='32,33');p.add_argument('--deadline-seconds',type=int,default=1200);p.add_argument('--check',type=Path)
 a=p.parse_args()
 if a.check:
  r=check(a.check);print(json.dumps(dict(status='CHECKED_COMPLETE_KERNEL_MASK_CHUNKING_SCOUT_NOT_PV',partitions=list(r['cases']))));return
 need(a.manifest is not None and a.out is not None,'manifest/out required');need(60<=a.deadline_seconds<=1800,'bounded deadline')
 m=strict(a.manifest);control=m['control_only'];need(type(control)is bool,'control flag')
 need((m['lo'],m['count'],m['partitions'])==((2,999,[2])if control else(38358837684,1000000,[1,2,8,16])),'fixed scientific universe')
 cpus=[int(x)for x in a.cpus.split(',')];need(len(cpus)==2 and len(set(cpus))==2 and set(cpus)<={32,33},'exact two CPUs')
 need(set(cpus)<=os.sched_getaffinity(0),'CPU applicability');root=Path(m['source_root']);out=a.out.resolve();need(not out.exists(),'fresh output required');out.mkdir(parents=True)
 need(m['baseline_sha256']=='2f6b880edf1b009758ccd4cac49644c299b02df3cfe52731e98c414dacc5775e' and sha(m['baseline_source'])==m['baseline_sha256'],'accepted baseline identity')
 records_by_name={x['module']:x for x in m['records']};need(len(records_by_name)==len(m['records']),'duplicate module')
 for x in m['records']:need(sha(x['source'])==x['sha256'],'proposal source changed')
 prefix_check='RamanujanPV.PackedMaskChunkControl'if control else'RamanujanPV.PackedMaskChunkPilot'
 common_text=Path(records_by_name[prefix_check+'.Common']['source']).read_text()
 need(re.search(r'def baselineValue : Nat := (0x[0-9a-f]+)',common_text)is not None,'standalone baseline data literal required')
 if not control:
  old_text=Path(m['baseline_source']).read_text()
  old_value=int(re.search(r'def bits : Nat := (0x[0-9a-f]+)',old_text).group(1),16)
  new_value=int(re.search(r'def baselineValue : Nat := (0x[0-9a-f]+)',common_text).group(1),16)
  need(old_value==new_value,'standalone original mask value mismatch')
 runner_sha=sha(__file__);helper_sha=sha(S/'scripts/compile_lean.py');generic_sha=sha(S/'RamanujanPV/PackedMaskChunks.lean');context_sha=sha(S/'BUILD_CONTEXT.json')
 opt=['-'+'O'*sys.flags.optimize]if sys.flags.optimize else[];start=time.monotonic();deadline=start+a.deadline_seconds;records=[];cases={};resource_samples=[];failures=[]
 def launch(module,cpu):
  resource=guard(96<<30);resource_samples.append(resource)
  need(time.monotonic()<deadline,'bounded dispatch deadline reached')
  command=[sys.executable]+opt+[str(S/'scripts/compile_lean.py'),module,'--source-root',str(root),'--audit-root',str(out/'audit'),'--cpus',str(cpu),'--memory-gib','48']
  child=subprocess.Popen(command,cwd=S,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
  while True:
   try:
    stdout,stderr=child.communicate(timeout=1);break
   except subprocess.TimeoutExpired:
    if time.monotonic()>=deadline:
     os.killpg(child.pid,signal.SIGTERM);stdout,stderr=child.communicate()
     censor=out/'censors';censor.mkdir(exist_ok=True)
     atomic(censor/(module+'.json'),dict(status='INTENTIONAL_BOUNDED_CENSOR_NOT_MATH_FAILURE',pid=child.pid,command=command,stdout=stdout.decode(errors='replace'),stderr=stderr.decode(errors='replace')))
     raise ValueError('bounded child deadline reached '+module)
  log=out/'controllers'/module;log.mkdir(parents=True,exist_ok=True);(log/'stdout').write_bytes(stdout);(log/'stderr').write_bytes(stderr)
  atomic(log/'OUTCOME.json',dict(module=module,command=command,pid=child.pid,returncode=child.returncode))
  need(child.returncode==0,'child failed '+module)
  line=stdout.decode().strip().splitlines()[-1];summary=strict_text(line);receipt=Path(summary['audit'])/'RUN.json';row=read_record(receipt,records_by_name.get(module,{}).get('sha256'),not module.endswith('.Data'))
  obj=Path('/data/ivy-ramanujan-source-pv-20261119/lean')/Path(*module.split('.')).with_suffix('.olean');need(obj.is_file(),'actual object missing')
  snapshot=out/'objects'/Path(*module.split('.')).with_suffix('.olean');snapshot.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj,snapshot)
  need(sha(snapshot)==strict(receipt)['object_sha256'],'compiler object hash mismatch')
  row.update(command=command,object_snapshot=str(snapshot),object_sha256=sha(snapshot),kind=records_by_name.get(module,{}).get('kind','typed_audit'))
  return row
 prefix='RamanujanPV.PackedMaskChunkControl'if control else'RamanujanPV.PackedMaskChunkPilot'
 def save():atomic(out/'PROGRESS.json',dict(status='PARTIAL_NOT_ACCEPTANCE',records=records,cases=cases,elapsed_seconds=time.monotonic()-start))
 try:
  common=launch(prefix+'.Common',cpus[0]);records.append(common);save()
  for k in m['partitions']:
   phase=time.monotonic();records.append(launch(prefix+f'.K{k}.Data',cpus[0]));save();pending=[prefix+f'.K{k}.Check{i:04d}'for i in range(k)];active={};free=list(cpus)
   with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
    while pending or active:
     guard(len(active)*(48<<30))
     while pending and free and not failures:
      need(time.monotonic()<deadline,'bounded dispatch deadline reached');cpu=free.pop(0);module=pending.pop(0);active[pool.submit(launch,module,cpu)]=(module,cpu)
     done,_=concurrent.futures.wait(active,timeout=1,return_when=concurrent.futures.FIRST_COMPLETED)
     for future in done:
      module,cpu=active.pop(future)
      try:records.append(future.result())
      except BaseException as error:failures.append(dict(module=module,error=repr(error)))
      free.append(cpu);save()
     if failures and not active:break
   need(not failures,'child failure; all active outcomes drained and collected')
   records.append(launch(prefix+f'.K{k}.Final',cpus[0]));case_records=[x for x in records if x['module'].startswith(prefix+f'.K{k}.')]
   cases[str(k)]=dict(partitions=k,wall_seconds_including_data_and_final=time.monotonic()-phase,sum_worker_elapsed_seconds=sum(x['elapsed_seconds']for x in case_records),peak_individual_worker_rss_bytes=max(x['peak_worker_rss_bytes']for x in case_records),shared_base_seconds=common['elapsed_seconds'],two_worker_maximum=True,complete_final_type=prefix+f'.K{k}.same_original_mask');save()
  audit_name=prefix+'.IndependentTypeAudit';audit_src=root/Path(*audit_name.split('.')).with_suffix('.lean');audit_src.parent.mkdir(parents=True,exist_ok=True)
  text=''.join(f'import {prefix}.K{k}.Final\n'for k in m['partitions']);text+=f'namespace {prefix}\n'
  for k in m['partitions']:
   text+=f'example : RamanujanPV.PackedSieveKernel.primeBits {m["lo"]} {m["count"]}={prefix}.baselineValue := K{k}.same_original_mask.trans expected_value\n#print axioms {prefix}.K{k}.same_original_mask\n'
  text+=f'end {prefix}\n';audit_src.write_text(text);records_by_name[audit_name]=dict(sha256=sha(audit_src),kind='typed_audit');records.append(launch(audit_name,cpus[0]))
  need(sha(__file__)==runner_sha and sha(S/'scripts/compile_lean.py')==helper_sha and sha(S/'RamanujanPV/PackedMaskChunks.lean')==generic_sha,'controller/generic bytes changed')
  result=dict(status='COMPLETE_KERNEL_MASK_CHUNKING_SCOUT_NOT_PV',control_only=control,manifest=str(a.manifest.resolve()),manifest_sha256=sha(a.manifest),runner_sha256=runner_sha,compile_helper_sha256=helper_sha,generic_math_sha256=generic_sha,context_sha256=context_sha,python_optimization=sys.flags.optimize,records=records,cases=cases,resource_samples=resource_samples,elapsed_seconds=time.monotonic()-start,per_worker_as_bytes=48<<30,max_workers=2,baseline_seconds=None if control else 133.06625039875507,scope='Same mathematical mask, lo/count/base/divisor indexing. Kernel scheduling only; no new source-first packed C PV or global finite count claim.')
  check_value(result);atomic(out/'RESULT.json',result);print(json.dumps(dict(status=result['status'],cases=cases)))
 except BaseException as error:
  for future,(module,cpu)in list(locals().get('active',{}).items()):
   if future.done()and module not in{r['module']for r in records}:
    try:records.append(future.result())
    except BaseException as child_error:
     if module not in{x['module']for x in failures}:failures.append(dict(module=module,error=repr(child_error)))
  atomic(out/'FAILED.json',dict(status='SCOUT_INCOMPLETE_OR_FAILED_NOT_ACCEPTANCE',error=repr(error),records=records,failures=failures,cases=cases,elapsed_seconds=time.monotonic()-start));raise
if __name__=='__main__':main()
