"""Rebuild the actual moment-program source extension of validated4057 evidence."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,importlib.util,json,math,os,re,shutil,subprocess,sys,time
B=Path(__file__).resolve().parent
STD3={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON '+k);d[k]=v
  return d
 def bad(s):raise ValueError('nonfiniteJSON '+s)
 def floating(s):
  v=float(s);need(math.isfinite(v),'overflowJSON');return v
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def strict(p):return parse(p.read_text())
def atomic(p,v):
 q=p.with_suffix('.pending');q.write_text(json.dumps(v,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def load(p,name):
 spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def inputs():
 lock=strict(B/'SOURCE_LOCK.json');parent=load(B/'base/reproduce.py','frozen4076');_,old,base,runner=parent.inputs()
 need(sha(B/'base/base/SOURCE_LOCK.json')==lock['base4057_source_lock_sha256']and sha(B/'base/SOURCE_LOCK.json')==lock['parent4076_source_lock_sha256'],'pinned validated4057 source/reproducer parent')
 sources=lock['sources'];names=[r['module']for r in sources];paths=[r['path']for r in sources];oldnames=set(lock['prior_module_names']);roots=lock['roots'];mods=lock['root_modules'];payloads=lock['payloads'];extra=[r['path']for r in payloads]
 need(len(names)==len(set(names))==429 and len(paths)==len(set(paths))==429,'unique429 sources')
 need(oldnames=={r['module']for r in base['combined_sources']}and len(oldnames)==4057 and not(set(names)&oldnames),'exact disjoint4057+429 sources')
 need(len(roots)==len(set(roots))==2835 and len(mods)==len(set(mods))==429 and set(mods)<=set(names),'unique full2835 roots/429 modules')
 need(len(extra)==len(set(extra))and not(set(extra)&set(paths)),'disjoint unique payload identities')
 public=set(lock['public_import_modules']);allowed={'Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Std','Init'}
 need(all(n.split('.')[0]in allowed for n in public),'known public import namespaces')
 for row in sources+payloads:
  rel=Path(row['path']);p=B/rel
  need(not rel.is_absolute()and'..'not in rel.parts and p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'exact source/payload '+str(rel))
 for row in sources:
  path=Path(row['source_root'])/Path(row['module'].replace('.','/')).with_suffix('.lean');need(path==Path(row['path']),'source/module/path correspondence')
  actual=[]
  for line in(B/row['path']).read_text().splitlines():
   match=re.match(r'^(?:public )?import\s+(.+)',line)
   if match:actual+=match.group(1).split('--')[0].split()
  need(all(n in names or n in oldnames or n in public for n in actual),'known complete import '+row['module'])
  need(row['imports']==[n for n in actual if n in names or n in oldnames],'exact actual application import edges')
 recipe=strict(B/'REPRODUCER_LOCK.json')
 for row in recipe['files']:
  p=B/row['path'];need(p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'exact active recipe '+row['path'])
 need(not list(B.rglob('*.olean'))and not list(B.rglob('*.o')),'source-only capsule/no application objects')
 native=load(B/'research/moment-hi-program-v1/reproduce_cpp_v2.py','native_entry');native.source_inputs()
 return lock,parent,base,runner

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--environment',type=Path);ap.add_argument('--base-run',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--jobs',type=int,default=8);ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args();need(1<=a.jobs<=12,'jobs1..12');lock,parent,base,runner=inputs();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh external owned output');out.mkdir(parents=True);logs=out/'logs';logs.mkdir();records=[];start=time.monotonic();flags=['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[]
 def execute(name,command,env=None):
  began=time.monotonic();so=logs/(name+'.stdout');se=logs/(name+'.stderr');tm=logs/(name+'.time')
  with so.open('wb')as f,se.open('wb')as g:q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*command],cwd=B,env=env,stdout=f,stderr=g)
  row=dict(name=name,command=command,exit_code=q.returncode,seconds=time.monotonic()-began,stdout_sha256=sha(so),stderr_sha256=sha(se),time_sha256=sha(tm))
  need(q.returncode==0,'failed '+name)
  need(not any(s in so.read_text(errors='replace')+se.read_text(errors='replace')for s in['sorryAx','Lean.ofReduceBool',"declaration uses 'sorry'",'declaration uses `sorry`']),'unproved/native diagnostic '+name)
  return row
 if a.check_inputs_only:
  records.append(execute('numerical-input-check',[sys.executable,*flags,str(B/'reproduce_numerics.py'),'--out',str(out/'native-input-check'),'--check-inputs-only']))
  records.append(execute('source-entry-input-check',[sys.executable,*flags,str(B/'research/moment-hi-program-v1/reproduce_cpp_v2.py'),'--out',str(out/'entry-input-check'),'--check-inputs-only']))
  atomic(out/'RECEIPT.json',dict(status='PASS4486_SOURCE_AND_REPRODUCER_IDENTITIES_ONLY_NOT_PROOF_REPLAY',source_modules=4486,new_source_modules=429,records=records,source_lock_sha256=sha(B/'SOURCE_LOCK.json')));return
 need(a.environment is not None and a.environment.is_file(),'pinned environment required');environment=runner.environment_inputs(a.environment.resolve(),base);compiler=environment['compiler'];bank=out/'objects';bank.mkdir();env=os.environ.copy();env['LEAN_PATH']=':'.join([str(bank)]+[d['objects']for d in environment['generic_dependencies']]);env['LEAN_NUM_THREADS']='1'
 try:
  prior=a.base_run.resolve()if a.base_run else out/'fresh4057'
  if a.base_run is None:
   jobs=str(a.jobs);records.append(execute('full4057',[sys.executable,*flags,str(B/'base/base/reproduce.py'),'--environment',str(a.environment.resolve()),'--out',str(prior),'--jobs',jobs,*sum(([('--'+k+'-jobs'),jobs]for k in['point','frame','edge','cell','weight','slope']),[])]))
  association=parent.validate_prior(prior,None,base,environment);atomic(out/'PRIOR_ASSOCIATION_BEFORE.json',association)
  for row in association['objects']:
   rel=Path(row['module'].replace('.','/')).with_suffix('.olean');dest=bank/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(prior/'objects'/rel,dest);need(sha(dest)==row['object_sha256'],'same validated source-built seed '+row['module'])
  clang=str(Path(compiler).with_name('clang'))
  records.append(execute('numerical-regeneration',[sys.executable,*flags,str(B/'reproduce_numerics.py'),'--compiler',clang,'--out',str(out/'numerics')]))
  numerical=strict(out/'numerics/RECEIPT.json');need(numerical['status']=='PASS_ALL_DETERMINISTIC_C_PROPOSALS_REGENERATED_AND_SOURCE_WORD_DATA_MATCHED','all768words/both769prefix regenerations')
  records.append(execute('source-build-link-run-association',[sys.executable,*flags,str(B/'research/moment-hi-program-v1/reproduce_cpp_v2.py'),'--compiler',clang,'--baseline',str(out/'numerics/height/run.stdout'),'--out',str(out/'actual-cpp')]))
  native=strict(out/'actual-cpp/RECEIPT.json');need(native['status']=='PASS_TWO_HIGH_ONLY_MOMENT_ENTRY_ASSOCIATIONS_AND_COMPLETE_BYTE_EQUIVALENCE_NOT_FORMAL_PROOF','both actual source/build/link/CRT/output associations')
  generated=out/'regenerated-source/SynergyMomentCHi/ObservedOutput.lean'
  records.append(execute('observed-source-regeneration',[sys.executable,*flags,str(B/'research/moment-hi-program-v1/generate_observation_v1.py'),'--run',str(out/'actual-cpp'),'--source',str(generated),'--receipt',str(out/'OBSERVATION_PREPARATION.json')]))
  observed=next(r for r in lock['sources']if r['module']=='SynergyMomentCHi.ObservedOutput');need(sha(generated)==observed['sha256'],'exact fresh native128-byte footer regenerated source identity')
  pending={r['module']:r for r in lock['sources']};need(len(pending)==429,'no module collapse');done=set();running={};oldnames=set(lock['prior_module_names'])
  def compile(row):
   p=B/row['path'];obj=bank/Path(row['module'].replace('.','/')).with_suffix('.olean');need(not obj.exists(),'no source shadowing');obj.parent.mkdir(parents=True,exist_ok=True);rec=execute(row['module'],[compiler,'-j1','-R',str(B/row['source_root']),str(p),'-o',str(obj)],env);rec.update(source_sha256=sha(p),object_sha256=sha(obj));return rec
  with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as ex:
   while pending or running:
    ready=[n for n,r in pending.items()if set(r['imports'])<=done|oldnames]
    for n in ready[:a.jobs-len(running)]:running[ex.submit(compile,pending.pop(n))]=n
    need(bool(running),'cycle/missing imports');completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
    for future in completed:
     n=running.pop(future);records.append(future.result());done.add(n);atomic(out/'PROGRESS.json',dict(status='PARTIAL_NOT_ACCEPTED',completed=len(done),total=429,seconds=time.monotonic()-start));atomic(out/'CHECKPOINT.json',dict(records=records))
  need(done=={r['module']for r in lock['sources']}and len(records)==432+int(a.base_run is None),'all429actual new compiles and3regenerations')
  audit=out/'Audit.lean';text=''.join('import '+n+'\n'for n in lock['root_modules'])+'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
  for begin in range(0,len(lock['roots']),64):text+='run_elab do\n let env ← getEnv\n for n in (['+','.join('`'+n for n in lock['roots'][begin:begin+64])+'] : List Name) do\n  let some ci := env.find? n | throwError "missing {n}"\n  let ax ← Lean.collectAxioms n\n  logInfo m!"MOMENT_SOURCE_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n'
  audit.write_text(text);records.append(execute('audit',[compiler,'-j1','-R',str(out),str(audit)],env));audits=[parse(l.split('MOMENT_SOURCE_AUDIT ',1)[1])for l in(logs/'audit.stdout').read_text().splitlines()if'MOMENT_SOURCE_AUDIT 'in l];need([r['name']for r in audits]==lock['roots']and all(set(r['axioms'])<=STD3 for r in audits),'all2835 actual typed complete standard closures')
  need({str(p.relative_to(bank))for p in bank.rglob('*.olean')}=={str(Path(n.replace('.','/')).with_suffix('.olean'))for n in oldnames|done},'exact4486 source-built bank')
  after=parent.validate_prior(prior,None,base,environment);need(after==association,'full prior association unchanged');atomic(out/'PRIOR_ASSOCIATION_AFTER.json',after);inputs();runner.environment_inputs(a.environment.resolve(),base)
 except Exception as ex:atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED_NOT_ACCEPTED',error=str(ex),records=records,seconds=time.monotonic()-start));raise
 # Numerical proposals and native binaries are regenerable. Preserve source,
 # accepted proofs, exact output+command receipts, compact observed bytes/logs.
 removed=[]
 for root in[out/'numerics',out/'actual-cpp']:
  for p in sorted(root.rglob('*')):
   if p.is_file()and((p.name in{'program','program.o','old-v1-program','prefix-proposal','prefix-proposal.cpp','old-v1-run.stdout','prefix-run.stdout'}or(root==out/'numerics'and p.name=='run.stdout'))):
    need(p.is_relative_to(root)and not p.is_symlink(),'owned cleanup');removed.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p)));p.unlink()
 result=dict(status='PASS4486_CHAINED_SOURCE_FIRST_MOMENT_PROGRAMS_TO_STRONGER_PNT',source_modules=4486,new_source_modules=429,new_selected_roots=2835,analytic_inputs=14,source_lock_sha256=sha(B/'SOURCE_LOCK.json'),reproducer_sha256=sha(Path(__file__)),reproducer_lock_sha256=sha(B/'REPRODUCER_LOCK.json'),prior_association_sha256=sha(out/'PRIOR_ASSOCIATION_BEFORE.json'),records=records,audits=audits,elapsed_seconds=time.monotonic()-start,same_pipeline_source_built_object_inputs=4057,outside_application_object_inputs=[],namespace_isolated=False,universal_host_IO_success=False,completed_source_graph=True,cleanup_removed=removed,qualification='Validated4057RO same-pipeline source-built evidence plus429new compiles; not empty-bank4486. Exact actual new source/build/link/CRT/run/footer-source and consumed read-to-ANT chain. Std3 final closures/no native execution axioms; same14 analytic premises. Precise Clang BitInt512/ABI/generic runtime/linkerCRT/OS/hardware and modeled normal stdio contracts remain. Namespace/resource receipts are separate.')
 atomic(out/'RECEIPT.json',result);print(json.dumps({k:result[k]for k in['status','source_modules','new_source_modules','new_selected_roots','elapsed_seconds']}))
if __name__=='__main__':main()
