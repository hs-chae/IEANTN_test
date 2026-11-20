#!/usr/bin/env python3
"""Deterministic generation and clean-source replay in an isolated workspace.

Full mode regenerates the actual9,676,151-record critical pair, both local
classification datasets and all adaptive cells, checks their accepted exact
source identities, then rebuilds the selected actual C-checker/math consumers
with no pre-existing application .oleans. Smoke mode is an explicit smaller
pipeline control and does not claim the full result.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def write(p,d):
 t=p.with_name(p.name+'.pending');need(not t.exists(),'fresh atomic stage');t.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');t.replace(p)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--mode',choices=['full','smoke'],default='full');p.add_argument('--prepare-only',action='store_true');p.add_argument('--jobs',type=int,default=6);p.add_argument('--memory-gib',type=int,default=48);p.add_argument('--cpus',default='72,73,74,75,76,77');a=p.parse_args();started=time.monotonic();out=a.out.resolve();need(not out.exists()and out.parent.is_dir(),'fresh existing-parent output');need(1<=a.jobs<=8 and 1<=a.memory_gib<=300 and a.jobs*a.memory_gib<=300,'bounded clean replay pool');cpus=[int(x)for x in a.cpus.split(',')];need(len(cpus)>=a.jobs and len(cpus)==len(set(cpus))and set(cpus)<=os.sched_getaffinity(0),'actual distinct available CPUs')
 context=read(a.context);reference=read(S/'BUILD_CONTEXT.json');need(context['compiler_sha256']==reference['compiler_sha256']and[(x['name'],x['revision'])for x in context['generic_dependencies']]==[(x['name'],x['revision'])for x in reference['generic_dependencies']],'exact pinned compiler/generic dependency universe');need(sha(context['compiler'])==context['compiler_sha256'],'actual compiler bytes');identities=read(S/'evidence/LOCAL_MILLION_REPRODUCTION_IDENTITIES.json');out.mkdir();workspace=out/'network/Solutions/RamanujanSourcePV.v1';workspace.parent.mkdir(parents=True);ignore=shutil.ignore_patterns('audit','.git','.lake','__pycache__','*.olean','*.ilean','*.o','*.bc');shutil.copytree(S,workspace,ignore=ignore);core=S.parents[1]/'IEANTN';shutil.copytree(core,out/'network/IEANTN',ignore=ignore);snapshots=[]
 for original,clone in [(S,workspace),(core,out/'network/IEANTN')]:
  for target in clone.rglob('*'):
   if not target.is_file():continue
   source=original/target.relative_to(clone);need(sha(source)==sha(target),'exact stable source snapshot');snapshots.append({'source':str(source),'clone':str(target),'sha256':sha(target)})
 write(out/'SOURCE_SNAPSHOT.json',{'stage':'INITIAL_SOURCE_COPY_BEFORE_EXPLICIT_BUILD_CONTEXT_REMAP','files':snapshots,'source_git_metadata_copied':False,'old_application_objects_copied':False});context=dict(context,new_application_object_root=str(out/'build/lean'));(workspace/'BUILD_CONTEXT.json').write_text(json.dumps(context,indent=2)+'\n');write(out/'PLAN.json',{'mode':a.mode,'full_math':identities['fixed_math'],'source_snapshot_sha256':sha(out/'SOURCE_SNAPSHOT.json'),'compiler_sha256':context['compiler_sha256'],'input_context_sha256':sha(a.context),'cloned_context_sha256':sha(workspace/'BUILD_CONTEXT.json'),'context_remap':'Only supplied clean-machine paths and fresh output object root; compiler SHA and generic revisions must equal original pins.','source_identity_lock_sha256':sha(workspace/'evidence/LOCAL_MILLION_REPRODUCTION_IDENTITIES.json'),'jobs':a.jobs,'memory_gib':a.memory_gib,'cpus':cpus,'script_sha256':sha(__file__),'qualification':'No original research checkout/source/objects are mutated. Full generation byte checks are mandatory; smoke does not establish the full theorem.'});logs=out/'commands';logs.mkdir();commands=[]
 flags=[]
 if sys.flags.optimize:flags=['-'+('O'*sys.flags.optimize)]
 def run(script,args):
  n=len(commands);cmd=[sys.executable,*flags,str(workspace/'scripts'/script),*map(str,args)];t=time.monotonic();r=subprocess.run(cmd,cwd=workspace,capture_output=True,text=True);so=logs/f'{n:02d}.stdout';se=logs/f'{n:02d}.stderr';so.write_text(r.stdout);se.write_text(r.stderr);record={'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-t,'stdout':str(so),'stdout_sha256':sha(so),'stderr':str(se),'stderr_sha256':sha(se)};commands.append(record);write(out/'COMMANDS.json',commands);need(r.returncode==0,'actual child command completion '+script)
 proposals=out/'proposals';proposals.mkdir();manifests={}
 def check(name,mpath):
  m=read(mpath)
  if a.mode=='full':
   fixed=identities['stages'][name];need({x['module']:x['sha256']for x in m['modules']}==fixed['modules'],'EXACT accepted generated Lean bytes '+name)
   if'packed_sha256'in fixed:need(m['packed_sha256']==fixed['packed_sha256'],'same exact arithmetic records')
   if'rows'in fixed:need(m['rows']==fixed['rows'],'same exact adaptive cells')
  manifests[name]=mpath
 # Regenerate actual source-first base count data; this proposer is UNTRUSTED.
 critical=proposals/'critical-raw';criticalpart=proposals/'critical'
 if a.mode=='full':
  run('generate_demand_certificate_resources.py',['--queries','38358837683,14111427770','--name','DemandCriticalPair','--out',critical,'--data-chunk',131072,'--proof-chunk',32768,'--max-records',100000000,'--cpus',','.join(map(str,cpus[:min(4,len(cpus))])),'--memory-gib',128])
 else:run('generate_demand_certificate.py',['--queries','1000,367','--name','DemandSmoke','--out',critical,'--data-chunk',256,'--proof-chunk',256,'--max-records',100000])
 run('partition_demand_proofs_context.py',['--owned-root',out,'--manifest',critical/'PROPOSAL.json','--out',criticalpart,'--subchunk',4096 if a.mode=='full' else 128,'--preserve-chunk',0,'--preserve-chunk',250]);check('critical',criticalpart/'PROPOSAL.json')
 control=proposals/'control';run('generate_local_prime_window.py',['--width',1000,'--name','LocalWindow1000B','--out',control,'--prime-chunk',128,'--data-chunk',256,'--check-chunk',256]);check('control',control/'PROPOSAL.json')
 controlcells=proposals/'control-cells';run('generate_window_cells.py',['--local-manifest',control/'PROPOSAL.json','--out',controlcells,'--namespace','RamanujanPV.LocalCells1000','--check-chunk',64]);check('control_cells',controlcells/'PROPOSAL.json')
 million=proposals/'million';width=1000000 if a.mode=='full' else 56;run('generate_local_prime_window.py',['--width',width,'--name','LocalWindowMillion','--out',million,'--prime-chunk',256,'--data-chunk',32768,'--check-chunk',32768]);check('million',million/'PROPOSAL.json')
 millioncells=proposals/'million-cells';run('generate_window_cells.py',['--local-manifest',million/'PROPOSAL.json','--out',millioncells,'--namespace','RamanujanPV.LocalCellsMillion','--check-chunk',64]);check('million_cells',millioncells/'PROPOSAL.json')
 merged=[]
 for name,mpath in manifests.items():
  m=read(mpath)
  for record in m['modules']:
   source=Path(record['source']);need(sha(source)==record['sha256'],'exact generated source before merge');target=workspace/Path(*record['module'].split('.')).with_suffix('.lean');need(not target.exists(),'unique generated module without source overwrite');target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target);merged.append({'module':record['module'],'sha256':sha(target),'source':str(target)})
 write(out/'GENERATED_SOURCES.json',{'mode':a.mode,'sources':merged,'exact_accepted_bytes_checked':a.mode=='full','old_application_objects_used':False});
 def validate_static_snapshot():
  for item in snapshots:
   target=Path(item['clone'])
   if target==workspace/'BUILD_CONTEXT.json':continue
   need(sha(target)==item['sha256'],'frozen cloned source/payload after generation and replay')
  need(sha(workspace/'BUILD_CONTEXT.json')==read(out/'PLAN.json')['cloned_context_sha256'],'explicit remapped context stable')
 validate_static_snapshot()
 if a.prepare_only:
  write(out/'PREPARED.json',{'status':'PREPARED_ONLY_NO_LEAN_REPLAY_OR_MATH_ACCEPTANCE','mode':a.mode,'commands':commands,'seconds':time.monotonic()-started});print('Prepared only; no Lean replay/result claimed.');return
 if a.mode=='full':roots=['RamanujanPV.MillionCriticalSourceClosed','RamanujanPV.SegmentSourceMargins','RamanujanPV.SegmentMillionDependencyAudit'];theorems=['RamanujanPV.MillionCriticalSourceClosed.real_interval','RamanujanPV.MillionCriticalSourceClosed.uniform_gap','RamanujanPV.MillionCriticalSourceClosed.p_endpoint_count','RamanujanPV.MillionCriticalSourceClosed.q_endpoint_count','RamanujanPV.SegmentRamanujanMillion.first_1000001_real_interval','RamanujanPV.SegmentSourceMargins.million_gap']
 else:roots=['RamanujanPV.DemandSmoke.Final','RamanujanPV.LocalCellsMillion.Final','RamanujanPV.QuotientDriverSuccess'];theorems=['RamanujanPV.DemandSmoke.pi_1000','RamanujanPV.DemandSmoke.pi_367','RamanujanPV.LocalCellsMillion.conditional_holds','RamanujanPV.QuotientDriverSuccess.successful_main_output']
 args=['--context',workspace/'BUILD_CONTEXT.json','--out',out/'build','--jobs',a.jobs,'--memory-gib',a.memory_gib,'--cpus',','.join(map(str,cpus))]
 for root in roots:args+=['--root',root]
 for theorem in theorems:args+=['--theorem',theorem]
 run('reproduce_parallel_closure.py',args);run('reproduce_parallel_closure.py',['--check',out/'build']);validate_static_snapshot();result=read(out/'build/RESULT.json');need(result['status']=='FRESH_SELECTED_SOURCE_CLOSURE_PASS'and result['old_application_objects_used']is False,'actual fresh selected source replay')
 write(out/'RESULT.json',{'status':'FULL_LOCAL_MILLION_GENERATION_AND_CLEAN_SOURCE_REPLAY_PASS'if a.mode=='full'else'SMOKE_PIPELINE_PASS_NOT_FULL_MILLION_REPLAY','mode':a.mode,'full_original_generated_source_bytes_checked':a.mode=='full','old_application_objects_used':False,'replay_result':str(out/'build/RESULT.json'),'replay_result_sha256':sha(out/'build/RESULT.json'),'source_snapshot_sha256':sha(out/'SOURCE_SNAPSHOT.json'),'generated_sources_sha256':sha(out/'GENERATED_SOURCES.json'),'commands':commands,'seconds':time.monotonic()-started,'script_sha256':sha(__file__)});print(json.dumps({'mode':a.mode,'status':'full replay passed'if a.mode=='full'else'smoke passed','seconds':time.monotonic()-started}))
if __name__=='__main__':main()
