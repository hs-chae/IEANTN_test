#!/usr/bin/env python3
"""Check every additive source scalar row, preserve original count-open scope.
This is a scoped source-proof overlay over independently accepted mathematical
inputs; it is not claimed to be a cold rebuild of the original application.
"""
from pathlib import Path
import argparse,concurrent.futures,datetime,hashlib,json,os,re,signal,subprocess,sys,time
from execute_full_scalar_certificate import read,sha,need,axioms,validate as validate_original
S=Path(__file__).resolve().parents[1]
STATUS='ALL_ORIGINAL_SCALAR_ROWS_SOURCE_EXECUTED_AND_9005_MARGIN_VERIFIED_COUNTS_OPEN'
def atomic(path,value):
 tmp=path.with_name(path.name+'.pending');tmp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');tmp.replace(path)
def expected_rows(blocks):
 def go(lo,hi):
  if hi-lo==1:
   n=blocks[lo]['namespace'];return '(RamanujanPV.FullFiniteScalars.rawRows '+n+'.rows '+n+'.count)'
  mid=(lo+hi)//2;return '('+go(lo,mid)+' ++ '+go(mid,hi)+')'
 return go(0,len(blocks))
def check(path):
 d=read(path);need(d['status']==STATUS and d['prime_counts_formally_proved_here']is False and d['source_first_scalar_PV']is True and d['complete_ANT_result']is False,'completed source scalar status/scope')
 need(sha(d['manifest'])==d['manifest_sha256'],'exact additive manifest');m=read(d['manifest']);need(m['schema']=='RAMANUJAN_FULL_SOURCE_SCALARS_PROPOSAL_V1','exact manifest schema')
 need(d['rows']==m['rows']and d['stop']==m['stop']and d['retained_integer_margin']==m['retained_integer_margin']==9005,'all rows/endpoints/margin')
 need(sha(m['original_manifest'])==m['original_manifest_sha256']and sha(m['original_result'])==m['original_result_sha256'],'preserved original inputs/results');validate_original(m['original_result'])
 need(len(d['records'])==len(m['modules'])+1,'every source and independent audit')
 old=read(m['original_manifest']);blocks=[x['original_block']for x in m['modules']if x['kind']=='block']
 need(blocks==old['blocks'][:len(blocks)]and sum(x['count']for x in blocks)==m['rows'],'exact original ordered full/control data')
 need(m['full_locked_prefix']==(old['full_locked_prefix']and len(blocks)==len(old['blocks']))and d['full_locked_prefix']==m['full_locked_prefix'],'exact full/control scope')
 need(type(d['jobs'])is int and 1<=d['jobs']<=32 and type(d['normal_worker_limit_bytes'])is int and d['combined_worker_limit_bytes']==d['jobs']*d['normal_worker_limit_bytes']and 0<d['combined_worker_limit_bytes']<=300*1024**3,'bounded aggregate resource policy')
 need(d['independent_audit']['expected_rows']==expected_rows(blocks),'independent exact original-row type target')
 for i,record in enumerate(d['records']):
  expected=m['modules'][i]if i<len(m['modules'])else d['independent_audit']
  need(record['module']==expected['module']and record['required_constants']==expected['standard_constants'],'complete exact declaration/type/axiom universe')
  receipt=Path(record['receipt']);need(sha(receipt)==record['receipt_sha256'],'receipt pin');r=read(receipt)
  need(r['status']=='COMPILED'and r['returncode']==0 and r['source_unchanged_during_compile']is True,'actual successful immutable source compile')
  need(sha(r['source'])==r['source_sha256']==expected['source_sha256']==sha(receipt.parent/'source.lean'),'actual current/snapshot source identity')
  need(sha(record['object'])==r['object_sha256'],'actual accepted object identity')
  need(r['compiler_sha256']==d['compiler_sha256']and r['generic_dependency_context_sha256']==d['context_sha256'],'exact compiler/dependency context association')
  need(type(record['memory_limit_bytes'])is int and record['memory_limit_bytes']==r['memory_limit_bytes']and 0<record['memory_limit_bytes']<=300*1024**3,'actual compiler memory cap association')
  need(record['affinity']==r['affinity']and len(record['affinity'])==1,'actual compiler CPU association')
  if i<len(m['modules'])-1:need(record['memory_limit_bytes']==d['normal_worker_limit_bytes'],'matched block resource limits')
  else:need(record['memory_limit_bytes']==d['final_independent_limit_bytes'],'exact final independent resource limits')
  need(sha(receipt.parent/'stdout')==r['stdout_sha256']and sha(receipt.parent/'stderr')==r['stderr_sha256']and sha(receipt.parent/'rusage.txt')==r['rusage_sha256'],'actual logs/resources')
  need(axioms((receipt.parent/'stdout').read_text(),expected['standard_constants'])==record['axioms'],'complete standard-only final/source axiom gates')
 need(sha(d['compiler'])==d['compiler_sha256'],'same exact compiler');need(sha(d['context'])==d['context_sha256'],'same exact build context')
 for name,pin in d['controller_dependencies'].items():need(sha(name)==pin,'same executed acceptance dependency')
 return dict(status='READBACK_PASS_ALL_SOURCE_SCALARS_COUNTS_OPEN',rows=d['rows'],margin=d['retained_integer_margin'],source_blocks=len(m['modules'])-1,result_sha256=sha(path))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path);p.add_argument('--out',type=Path);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--jobs',type=int,default=12);p.add_argument('--memory-gib',type=int,default=24);p.add_argument('--cpus',default=','.join(map(str,range(52,64))));p.add_argument('--allow-profile',action='store_true');p.add_argument('--check',type=Path);a=p.parse_args()
 if a.check:
  need(a.manifest is None and a.out is None,'separate read-only route');print(json.dumps(check(a.check)));return
 need(a.manifest is not None and a.out is not None,'manifest and fresh run output required')
 m=read(a.manifest);need(m['schema']=='RAMANUJAN_FULL_SOURCE_SCALARS_PROPOSAL_V1'and m['status']=='UNTRUSTED_REQUIRES_ALL_ADDITIVE_KERNEL_SOURCE_EXECUTION_PROOFS','exact additive source proposal')
 need(m['prime_counts_formally_proved_here']is False and m['retained_integer_margin']==9005,'source scalar-only scientific scope')
 need(a.allow_profile or(m['full_locked_prefix']is True and m['rows']==1755663 and m['stop']==1490000000001),'entire locked prefix or explicit bounded control')
 need(sha(m['original_manifest'])==m['original_manifest_sha256']and sha(m['original_result'])==m['original_result_sha256'],'original inputs/results unchanged');validate_original(m['original_result']);old=read(m['original_manifest']);blocks=[x['original_block']for x in m['modules']if x['kind']=='block'];need(blocks==old['blocks'][:len(blocks)]and sum(x['count']for x in blocks)==m['rows'],'all original ordered rows/blocks')
 root=Path(m['source_root']);need(set(root.rglob('*.lean'))=={Path(x['source'])for x in m['modules']},'complete exact written source universe')
 need([x['kind']for x in m['modules']]==['block']*len(blocks)+['final'],'all blocks and one final consumer')
 for x in m['modules']:need(sha(x['source'])==x['source_sha256'],'immutable proposed source')
 context=read(a.context);compiler=Path(context['compiler']);need(sha(compiler)==context['compiler_sha256'],'actual pinned compiler');objects=Path(context['new_application_object_root']);out=a.out.resolve();need(not out.exists()and out.is_relative_to(objects.resolve().parent),'fresh context-owned run output')
 cpus=list(map(int,a.cpus.split(',')));need(1<=a.jobs<=32 and 1<=a.memory_gib<=300 and a.jobs*a.memory_gib<=300,'authorized bounded aggregate');need(len(cpus)==len(set(cpus))and len(cpus)>=a.jobs and set(cpus)<=os.sched_getaffinity(0),'actual distinct available CPUs')
 available=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024
 need(available>=1024**4 and available>=(512+max(a.jobs*a.memory_gib,192))*1024**3,'genuinely available RAM and512GiB host reserve')
 out.mkdir(parents=True);(out/'logs').mkdir();started=time.monotonic();dependency_paths=[Path(__file__).resolve(),S/'scripts/execute_full_scalar_certificate.py',S/'scripts/compile_lean_context.py'];pins={str(x):sha(x)for x in dependency_paths};drain=[]
 def on_signal(sig,_):drain.append(sig)
 for sig in [signal.SIGUSR1,signal.SIGTERM,signal.SIGINT]:signal.signal(sig,on_signal)
 def compile_one(x,cpu,limit):
  for name,pin in pins.items():need(sha(name)==pin,'controller/helper changed during actual run')
  module=x['module'];command=[sys.executable,str(S/'scripts/compile_lean_context.py'),module,'--context',str(a.context.resolve()),'--source-root',str(x['source_root']),'--audit-root',str(out/'audit'),'--cpus',str(cpu),'--memory-gib',str(limit)]
  with(out/'logs'/(module+'.stdout')).open('w')as so,(out/'logs'/(module+'.stderr')).open('w')as se:done=subprocess.run(command,stdout=so,stderr=se)
  receipt=out/'audit'/module/'1/RUN.json';need(done.returncode==0 and receipt.is_file(),'actual compiler failure '+module);r=read(receipt);need(r['status']=='COMPILED'and r['source_sha256']==x['source_sha256'],'exact successful proposed source');names=x['standard_constants']
  rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',(receipt.parent/'rusage.txt').read_text());need(rss is not None,'actual peak RAM receipt')
  return dict(module=module,receipt=str(receipt),receipt_sha256=sha(receipt),object=str(objects/Path(*module.split('.')).with_suffix('.olean')),required_constants=names,axioms=axioms((receipt.parent/'stdout').read_text(),names),seconds=r['elapsed_seconds'],actual_peak_worker_rss_bytes=int(rss.group(1))*1024,memory_limit_bytes=limit*1024**3,affinity=[cpu])
 records={};pending=list(m['modules'][:-1]);running={};free=cpus[:a.jobs]
 try:
  with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as pool:
   while pending or running:
    while pending and free and not drain:
     x=pending.pop(0);cpu=free.pop(0);running[pool.submit(compile_one,x,cpu,a.memory_gib)]=(x,cpu)
    if not running:break
    done,_=concurrent.futures.wait(running,timeout=5,return_when=concurrent.futures.FIRST_COMPLETED)
    for f in done:
     x,cpu=running.pop(f);records[x['module']]=f.result();free.append(cpu)
    atomic(out/'PROGRESS.json',dict(status='ACTUAL_SOURCE_SCALAR_PROOFS_RUNNING',controller_pid=os.getpid(),completed=len(records),total=len(m['modules']),running_modules=[x['module']for x,_ in running.values()],pending=len(pending),drain_signals=drain,seconds=time.monotonic()-started))
  if drain:
   atomic(out/'DRAINED.json',dict(status='CURRENT_SOURCE_PROOFS_DRAINED_NO_FINAL_ACCEPTANCE',completed=len(records),pending=len(pending),signals=drain));return
  final=m['modules'][-1];records[final['module']]=compile_one(final,cpus[0],192)
  audit_root=out/'independent-source';audit=audit_root/Path(*m['namespace'].split('.'))/'ControllerAudit.lean';audit.parent.mkdir(parents=True)
  audit.write_text('import '+m['final_module']+'\nexample : RamanujanPV.FullFiniteSourcePV.SourceMarginCertificate '+str(m['begin'])+' '+str(m['stop'])+' 9005 '+expected_rows(blocks)+' := '+m['namespace']+'.all_source_margins\n#print axioms '+m['namespace']+'.all_source_margins\n#print axioms '+m['namespace']+'.all_source_scalars\n')
  ar=dict(module=m['namespace']+'.ControllerAudit',source=str(audit),source_sha256=sha(audit),source_root=str(audit_root),standard_constants=[m['namespace']+'.all_source_margins',m['namespace']+'.all_source_scalars'],expected_rows=expected_rows(blocks));independent=compile_one(ar,cpus[0],192)
  ordered=[records[x['module']]for x in m['modules']]+[independent]
  for name,pin in pins.items():need(sha(name)==pin,'same executed validator before final receipt')
  result=dict(status=STATUS,manifest=str(a.manifest.resolve()),manifest_sha256=sha(a.manifest),rows=m['rows'],stop=m['stop'],full_locked_prefix=m['full_locked_prefix'],retained_integer_margin=9005,prime_counts_formally_proved_here=False,source_first_scalar_PV=True,complete_ANT_result=False,jobs=a.jobs,records=ordered,independent_audit=ar,seconds=time.monotonic()-started,controller_dependencies=pins,context=str(a.context.resolve()),context_sha256=sha(a.context),compiler=str(compiler),compiler_sha256=context['compiler_sha256'],combined_worker_limit_bytes=a.jobs*a.memory_gib*1024**3,normal_worker_limit_bytes=a.memory_gib*1024**3,final_independent_limit_bytes=192*1024**3,host_memavailable_before_bytes=available,host_reserve_bytes=512*1024**3,actual_peak_worker_rss_bytes=max(x['actual_peak_worker_rss_bytes']for x in ordered),aggregate_actual_peak_RAM_measured=False,oom_events=[],timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
  result['owned_source_run_and_new_objects_bytes']=sum(p.stat().st_size for p in root.rglob('*')if p.is_file())+sum(p.stat().st_size for p in out.rglob('*')if p.is_file())+sum(Path(x['object']).stat().st_size for x in ordered)
  candidate=out/'RESULT.pending'
  atomic(candidate,result)
  validated=check(candidate)
  candidate.replace(out/'RESULT.json')
  print(json.dumps(validated))
 except Exception as error:
  atomic(out/'FAILED.json',dict(status='FAILED_ATTEMPT_PRESERVED_NO_SOURCE_SCALAR_ACCEPTANCE',reason=str(error),completed=list(records),seconds=time.monotonic()-started));raise
if __name__=='__main__':main()
