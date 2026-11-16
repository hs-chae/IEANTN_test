"""Clean-source continuation of the frozen4057 source-main graph to two ANT consumers."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,sys,time,tempfile,re,math
B=Path(__file__).resolve().parent;STD3={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse_strict(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key '+k);d[k]=v
  return d
 def bad(s):raise ValueError('nonfinite JSON '+s)
 def floating(s):
  value=float(s);need(math.isfinite(value),'nonfinite JSON float '+s);return value
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def strict(p):return parse_strict(p.read_text())
def atomic(p,a):
 t=p.with_suffix('.pending');t.write_text(json.dumps(a,indent=2)+'\n');os.replace(t,p)
def parent():
 spec=importlib.util.spec_from_file_location('locked4057',B/'base/reproduce.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def inputs():
 lock=strict(B/'SOURCE_LOCK.json');m=parent();base,runner=m.source_inputs()
 need(sha(B/'base/SOURCE_LOCK.json')==lock['base4057_source_lock_sha256'],'exact frozen4057 parent')
 need(len(lock['shared_sources'])==10 and len(lock['branch_sources'])==9 and len(base['combined_sources'])==4057,'exact4076written sources')
 for row in lock['shared_sources']+lock['branch_sources']:
  p=B/row['path'];need(p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'source identity '+row['path'])
 for row in strict(B/'INPUT_FILES_V1.json')['files']:
  p=B/row['path'];need(p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'recipe identity '+row['path'])
 need(not list(B.rglob('*.olean')),'no application objects in source capsule')
 return lock,m,base,runner

def validate_regeneration(run,base,environment,vi,vo,records):
 source=B/'base/base/base/base';numerics=source/'numerics';manifest=strict(numerics/'HEIGHT_REGEN_MANIFEST_V1.json');nr=strict(run/'numerics/RECEIPT.json');pin=strict(source/'CPP_ASSOCIATION_PIN.json');cc=str(Path(environment['compiler']).with_name('clang'))
 need(sha(Path(cc))==manifest['compiler_sha256']==pin['compiler_sha256'],'pinned actual clang identity')
 need(nr['status']=='ALL_FIVE_RAW_REGENERATIONS_PASS'and nr['manifest_sha256']==sha(numerics/'HEIGHT_REGEN_MANIFEST_V1.json')and nr['script_sha256']==sha(numerics/'reproduce_height_numerics_v1.py')and nr['compiler_sha256']==manifest['compiler_sha256']and nr['parameters']==manifest['parameters'],'exact numerical generator receipt/source/parameters')
 opt=nr['python_optimization'];need(type(opt)is int and opt in[0,1,2],'recorded optimization mode');flags=[]if opt==0 else['-O'if opt==1 else'-OO'];python=records['numerical-regeneration']['command'][0]
 need(Path(python).is_file(),'recorded generic Python interpreter available')
 commands={
  'numerical-regeneration':[python,*flags,str(vi/'base/base/base/numerics/reproduce_height_numerics_v1.py'),'--compiler',cc,'--out',str(vo/'numerics')],
  'numerical-word-association':[python,*flags,str(vi/'base/base/base/numerics/verify_regenerated_height_words_v1.py'),'--source-root',str(vi/'base/base/base/source'),'--raw-root',str(vo/'numerics'),'--out',str(vo/'NUMERICAL_WORD_ASSOCIATION.json')],
  'actual-cpp-regeneration':[python,*flags,str(vi/'base/base/base/reproduce_cpp.py'),'--compiler',cc,'--out',str(vo/'actual-cpp')],
  'observed-source-regeneration':[python,*flags,str(vi/'base/regenerate_observation.py'),'--run',str(vo/'actual-cpp'),'--out',str(vo/'observation'),'--source-output',str(vo/'regenerated-source/SynergyHeightC/MainObservedOutput.lean')]}
 need(all(records[n]['command']==cmd and records[n]['exit_code']==0 for n,cmd in commands.items()),'all four exact regeneration command/script/output routes')
 need(len(nr['records'])==len(manifest['programs'])==5 and[x['name']for x in nr['records']]==[x['name']for x in manifest['programs']],'exact five numerical generators')
 for expected,row in zip(manifest['programs'],nr['records']):
  name=row['name'];raw=run/'numerics'/name/'output.bin';recorded_binary=vo/'numerics'/name/'program'
  need(row==strict(run/'numerics'/name/'RECEIPT.json')and row['status']=='EXACT_RAW_REGENERATION_PASS'and row['source_sha256']==expected['source_sha256']==sha(numerics/expected['source'])and row['output_sha256']==expected['output_sha256']==sha(raw)and row['output_bytes']==raw.stat().st_size,'exact numerical source/raw-output/receipt '+name)
  need(row['compile_command']==[cc,*manifest['compiler_flags'],str(vi/'base/base/base/numerics'/expected['source']),'-o',str(recorded_binary)]and row['run_command']==['/usr/bin/time','-v',str(recorded_binary)]and re.fullmatch(r'[0-9a-f]{64}',row['binary_sha256'])is not None,'exact numerical compile/run '+name)
 for path,digest in manifest['includes'].items():need(sha(numerics/path)==digest,'numerical application include '+path)
 wr=strict(run/'NUMERICAL_WORD_ASSOCIATION.json');source_modules=['HeightPointChecks','HeightPointConstants','HeightPointGrid','HeightPointLogGridDefs','HeightBudgetBlocks'];expected_sources={str(vi/'base/base/base/source/SynergyAnalytic'/(n+'.lean')):sha(source/'source/SynergyAnalytic'/(n+'.lean'))for n in source_modules}
 need(wr['status']=='ALL_REGENERATED_WORDS_MATCH_KERNEL_PROPOSALS'and wr['source_files']==expected_sources and wr['point_cells']==768 and wr['constant_boxes']==58 and wr['budget_blocks']==24 and wr['h_and_q_boxes']==2 and wr['python_optimization']==opt,'all exact original source-word association routes')
 cr=strict(run/'actual-cpp/RECEIPT.json');raw=run/'actual-cpp/output.bin';tree=source/'height-bundle-source-v3'
 need({p.name:sha(p)for p in tree.iterdir()if p.is_file()}==pin['physical_C_files'],'exact actual compiled C source tree')
 need(cr['status']=='RAW_ACTUAL_CPP_OUTPUT_ASSOCIATION_PASS'and cr['source_first_PV']is False and cr['output_sha256']==sha(raw)==pin['expected_output_sha256']and raw.stat().st_size==98432 and cr['verified_regenerable_binary_removed']is True and re.fullmatch(r'[0-9a-f]{64}',cr['binary_sha256'])is not None,'actual full C output/receipt identity')
 binary=vo/'actual-cpp/height-program';need(cr['commands']==[[cc,*pin['compiler_flags'],str(vi/'base/base/base/height-bundle-source-v3/height_bundle.cpp'),'-o',str(binary)],[str(binary)]],'exact actual C compile/run route')
 observed=strict(run/'observation/PREPARATION.json');tail=raw.read_bytes()[-128:];observed_source=run/'regenerated-source/SynergyHeightC/MainObservedOutput.lean';locked_source=B/'base/base/source/SynergyHeightC/MainObservedOutput.lean'
 need(observed['status']=='OBSERVATION_PREPARED_REQUIRES_LEAN_SOURCE_COMPARISON'and observed['script_sha256']==sha(B/'base/base/regenerate_observation.py')and observed['raw_receipt']=='actual-cpp/RECEIPT.json'and observed['raw_receipt_sha256']==sha(run/'actual-cpp/RECEIPT.json')and observed['physical_output']=='actual-cpp/output.bin'and observed['physical_output_bytes']==98432 and observed['physical_output_sha256']==sha(raw),'observed-source/raw-run receipt association')
 need(observed['total_observation_bytes']==128 and(run/'observation/observed-total.bin').read_bytes()==tail and observed['total_observation_sha256']==sha(run/'observation/observed-total.bin')and observed['lo']==str(int.from_bytes(tail[:64],'little'))and observed['hi']==str(int.from_bytes(tail[64:],'little')),'actual physical final128bytes/words')
 need(observed['source_trees']==['base/base/height-bundle-source-v3']and observed['source']=='regenerated-source/SynergyHeightC/MainObservedOutput.lean'and observed['source_sha256']==sha(observed_source)==sha(locked_source)and observed['source_pin_sha256']==sha(source/'CPP_ASSOCIATION_PIN.json')and observed['compiler']==cc and observed['compiler_sha256']==sha(Path(cc)),'exact regenerated observed-source/compiler/source-pin identity')
 # Exercise the existing deterministic word checker and observation generator again.
 # Their only fresh outputs are small, regenerable validation temporaries.
 with tempfile.TemporaryDirectory(prefix='ieantn-owned-base-recheck-')as tmp:
  t=Path(tmp);q=subprocess.run([sys.executable,*flags,str(numerics/'verify_regenerated_height_words_v1.py'),'--source-root',str(source/'source'),'--raw-root',str(run/'numerics'),'--out',str(t/'word-check.json')],capture_output=True,text=True);need(q.returncode==0 and strict(t/'word-check.json')['status']=='ALL_REGENERATED_WORDS_MATCH_KERNEL_PROPOSALS','fresh exact-word recheck')
  copied=t/'actual-cpp';copied.mkdir();shutil.copy2(run/'actual-cpp/RECEIPT.json',copied/'RECEIPT.json');shutil.copy2(raw,copied/'output.bin');generated=t/'regenerated-source/SynergyHeightC/MainObservedOutput.lean';q=subprocess.run([sys.executable,*flags,str(B/'base/base/regenerate_observation.py'),'--run',str(copied),'--out',str(t/'observation'),'--source-output',str(generated)],capture_output=True,text=True);need(q.returncode==0 and sha(generated)==sha(locked_source),'fresh exact observed-source regeneration')
 return dict(status='ALL_FOUR_RECORDED_REGENERATION_ROUTES_AND_FRESH_WORD_OBSERVATION_RECHECK_PASS',numerical_manifest_sha256=sha(numerics/'HEIGHT_REGEN_MANIFEST_V1.json'),actual_C_pin_sha256=sha(source/'CPP_ASSOCIATION_PIN.json'),observed_source_sha256=sha(observed_source),observed_preparation_sha256=sha(run/'observation/PREPARATION.json'),recorded_python_sha256=sha(Path(python)),actual_clang_sha256=sha(Path(cc)))

def expected_parent_audit(base):
 roots=base['combined_roots'];text=''.join('import '+n+'\n'for n in base['combined_root_modules'])
 text+='import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 for begin in range(0,len(roots),64):
  text+='run_elab do\n let env ← getEnv\n for n in (['+','.join('`'+n for n in roots[begin:begin+64])
  text+='] : List Name) do\n  let some _ := env.find? n | throwError "missing {n}"\n'
  text+='  let ax ← Lean.collectAxioms n\n  logInfo m!"RATIONAL_AUDIT {(Json.mkObj [("name",toJson n.toString),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n'
 return text

def validate_prior(run,lock,base,environment):
 r=strict(run/'RECEIPT.json');need(r['status']=='PASS4057_FRESH_SOURCE_MAIN_OBSERVED_RATIONAL_ANT'and r['source_modules']==4057 and r['selected_theorem_roots']==12234 and r['application_object_inputs']==[]and r['completed_fresh_source_graph'],'completed fresh4057 parent required')
 need(r['source_lock_sha256']==sha(B/'base/SOURCE_LOCK.json')and r['reproducer_sha256']==sha(B/'base/reproduce.py')and r['reproducer_lock_sha256']==sha(B/'base/REPRODUCER_LOCK.json'),'exact parent source/recipe identities')
 records=r['records'];byname={x['name']:x for x in records};need(len(records)==len(byname)==4062,'4057actual compiles plus4regenerations+audit')
 objects=[];virtual_input=None;virtual_output=None
 for row in base['combined_sources']:
  name=row['module'];q=byname[name];cmd=q['command'];rel=Path(name.replace('.','/')).with_suffix('.lean');obj=run/'objects'/rel.with_suffix('.olean')
  need(q['exit_code']==0 and q['source_sha256']==row['sha256']and len(cmd)==7 and cmd[1:3]==['-j1','-R']and cmd[5]=='-o','exact compiler invocation '+name)
  need(cmd[0]==environment['compiler']and sha(Path(cmd[0]))==base['compiler_sha256'],'pinned actual compiler path/hash '+name)
  suffix='/'+row['source_root'];need(str(Path(cmd[3])).endswith(suffix),'recorded source root '+name)
  vi=Path(str(Path(cmd[3]))[:-len(suffix)]);obj_suffix='/objects/'+str(rel.with_suffix('.olean'));need(str(Path(cmd[6])).endswith(obj_suffix),'recorded output object '+name);vo=Path(str(Path(cmd[6]))[:-len(obj_suffix)])
  if virtual_input is None:virtual_input,virtual_output=vi,vo
  need((vi,vo)==(virtual_input,virtual_output)and Path(cmd[4])==vi/row['path']and Path(cmd[3])==vi/row['source_root'],'one exact recorded source/output tree '+name)
  need(obj.is_file()and not obj.is_symlink()and sha(obj)==q['object_sha256'],'same source-built parent object '+name);objects.append(dict(module=name,source_sha256=row['sha256'],object_sha256=sha(obj)))
 for q in records:
  need(q['exit_code']==0,'completed parent record '+q['name'])
  for suffix,k in[('.stdout','stdout_sha256'),('.stderr','stderr_sha256'),('.time','time_sha256')]:need(sha(run/'logs'/(q['name']+suffix))==q[k],'exact parent log '+q['name'])
 need(byname['audit']['command']==[environment['compiler'],'-j1','-R',str(virtual_output),str(virtual_output/'Audit.lean')]and(run/'Audit.lean').read_text()==expected_parent_audit(base),'exact pinned parent audit compiler/command/generated source')
 audits=[strict_line(s.split('RATIONAL_AUDIT ',1)[1])for s in(run/'logs/audit.stdout').read_text().splitlines()if'RATIONAL_AUDIT 'in s]
 need(audits==r['audits']and[x['name']for x in audits]==base['combined_roots']and len(audits)==12234 and all(set(x['axioms'])<=STD3 for x in audits),'actual12234complete standard parent closures')
 need({str(p.relative_to(run/'objects'))for p in(run/'objects').rglob('*.olean')}=={str(Path(x['module'].replace('.','/')).with_suffix('.olean'))for x in objects},'exact parent source-built population')
 numeric=run/'numerics/RECEIPT.json';words=run/'NUMERICAL_WORD_ASSOCIATION.json';cpp=run/'actual-cpp/RECEIPT.json'
 regeneration=validate_regeneration(run,base,environment,virtual_input,virtual_output,byname)
 return dict(parent_receipt_sha256=sha(run/'RECEIPT.json'),parent_source_lock_sha256=sha(B/'base/SOURCE_LOCK.json'),objects=objects,numerical_receipt_sha256=sha(numeric),numerical_word_association_sha256=sha(words),actual_cpp_receipt_sha256=sha(cpp),regeneration=regeneration)
def strict_line(text):return parse_strict(text)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--environment',type=Path);ap.add_argument('--base-run',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--jobs',type=int,default=3);ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args();lock,m,base,runner=inputs();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh output outside immutable capsule');need(1<=a.jobs<=16,'jobs1..16');out.mkdir(parents=True)
 if a.check_inputs_only:atomic(out/'RECEIPT.json',dict(status='PASS4076_SOURCE_IDENTITIES_ONLY_NOT_REPLAY',written_sources=4076,proof_replay=False,application_object_inputs=[],source_lock_sha256=sha(B/'SOURCE_LOCK.json')));return
 need(a.environment is not None and a.environment.is_file(),'pinned public environment required');environment=runner.environment_inputs(a.environment.resolve(),base);compiler=environment['compiler'];logs=out/'logs';logs.mkdir();records=[];start=time.monotonic();flags=['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[]
 def execute(name,command,env=None):
  began=time.monotonic()
  with(logs/(name+'.stdout')).open('w')as so,(logs/(name+'.stderr')).open('w')as se:q=subprocess.run(['/usr/bin/time','-v','-o',str(logs/(name+'.time')),*command],cwd=B,env=env,stdout=so,stderr=se)
  row=dict(name=name,command=command,exit_code=q.returncode,seconds=time.monotonic()-began,stdout_sha256=sha(logs/(name+'.stdout')),stderr_sha256=sha(logs/(name+'.stderr')),time_sha256=sha(logs/(name+'.time')));records.append(row);atomic(out/'PROGRESS.json',dict(status='PARTIAL_NOT_ACCEPTED',records=records,seconds=time.monotonic()-start));need(q.returncode==0,'failed '+name)
  need(not any(t in(logs/(name+'.stdout')).read_text()+(logs/(name+'.stderr')).read_text()for t in['sorryAx','Lean.ofReduceBool',"declaration uses 'sorry'",'declaration uses `sorry`']),'admitted/native diagnostic '+name);return row
 def make_env(bank):
  e=os.environ.copy();e['LEAN_PATH']=':'.join([str(bank)]+[d['objects']for d in environment['generic_dependencies']]);e['LEAN_NUM_THREADS']='1';return e
 def compile_one(row,bank,label):
  p=B/row['path'];obj=bank/Path(row['module'].replace('.','/')).with_suffix('.olean');need(not obj.exists(),'no application shadowing '+row['module']);obj.parent.mkdir(parents=True,exist_ok=True);r=execute(label+'-'+row['module'],[compiler,'-j1','-R',str(B/row['source_root']),str(p),'-o',str(obj)],make_env(bank));r.update(source_sha256=sha(p),object_sha256=sha(obj))
 def audit_roots(name,br,bank,modules,roots):
  p=br/'Audit.lean';text=''.join('import '+x+'\n'for x in dict.fromkeys(modules))+'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
  for begin in range(0,len(roots),32):text+='run_elab do\n let env ← getEnv\n for n in (['+','.join('`'+x for x in roots[begin:begin+32])+'] : List Name) do\n  let some _ := env.find? n | throwError "missing {n}"\n  let ax ← Lean.collectAxioms n\n  logInfo m!"SOURCE_ANT_AUDIT {(Json.mkObj [("name",toJson n.toString),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n'
  p.write_text(text);execute(name+'-audit',[compiler,'-j1','-R',str(br),str(p)],make_env(bank));rows=[strict_line(s.split('SOURCE_ANT_AUDIT ',1)[1])for s in(logs/(name+'-audit.stdout')).read_text().splitlines()if'SOURCE_ANT_AUDIT 'in s];need([x['name']for x in rows]==roots and all(set(x['axioms'])<=STD3 for x in rows),'all selected source/ANT closures standard');return rows
 try:
  run=a.base_run.resolve()if a.base_run else out/'fresh4057'
  if not a.base_run:
   jobs=str(a.jobs);execute('full4057',[sys.executable,*flags,str(B/'base/reproduce.py'),'--environment',str(a.environment.resolve()),'--out',str(run),'--jobs',jobs,*sum(([('--'+k+'-jobs'),jobs]for k in['point','frame','edge','cell','weight','slope']),[])])
  association=validate_prior(run,lock,base,environment);atomic(out/'BASE_ASSOCIATION.json',association);shared=out/'shared';bank=shared/'objects';bank.mkdir(parents=True)
  for row in association['objects']:
   rel=Path(row['module'].replace('.','/')).with_suffix('.olean');dest=bank/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(run/'objects'/rel,dest);need(sha(dest)==row['object_sha256'],'same-pipeline source seed')
  for row in lock['shared_sources']:compile_one(row,bank,'shared')
  roots=[x for r in lock['shared_sources']for x in r['roots']];modules=[r['module']for r in lock['shared_sources']];shared_audits=audit_roots('shared',shared,bank,modules,roots);branches=[]
  shared_objects={str(p.relative_to(bank)):sha(p)for p in bank.rglob('*.olean')};need(len(shared_objects)==4067,'4057+10 source-built shared bank')
  for branch in lock['branches']:
   name=branch['name'];br=out/name;target=br/'objects';target.mkdir(parents=True)
   for rel,digest in shared_objects.items():
    p=target/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(bank/rel,p);need(sha(p)==digest,'same-pipeline coherent branch seed')
   for identity in branch['source_order']:compile_one(next(x for x in lock['branch_sources']if x['identity']==identity),target,name)
   audits=audit_roots(name,br,target,modules+branch['root_modules'],roots+branch['roots']);branches.append(dict(name=name,source_modules=4067+len(branch['source_order']),audits=audits,outside_application_object_inputs=[]))
  inputs();need(validate_prior(run,lock,base,environment)==association,'all prior source/command/object/log/audit evidence unchanged after consumers');need({str(p.relative_to(bank)):sha(p)for p in bank.rglob('*.olean')}==shared_objects,'shared source-built bank unchanged')
  result=dict(status='PASS_SOURCE4076_SAME_PIPELINE_MAIN_READ_TO_TWO_ANT_CONSUMERS',written_source_files=4076,seconds=time.monotonic()-start,records=records,shared_audits=shared_audits,branches=branches,source_lock_sha256=sha(B/'SOURCE_LOCK.json'),reproducer_sha256=sha(Path(__file__)),base_association_sha256=sha(out/'BASE_ASSOCIATION.json'),base_source_built_modules=4057,shared_source_built_modules=4067,outside_application_object_inputs=[],namespace_isolated=False,same14_analytic_inputs=True,C_source_algorithm_output_unchanged=True,original_exposure_outcomes_unchanged=True,qualification='Completed chained source-only replay; existing physical C run/observed footer regenerated in the validated4057 base. New read consumers genuinely use read-derived pi/psi300. Separate coherent per-node banks; constructed successful stdio scenario and pinned generic compiler/runtime/kernel/ABI/OS/hardware trust remain. Namespace isolation is separately attested. Original8192/16384 Scoped Winner body migration not implied.')
  atomic(out/'RECEIPT.json',result);print(result['status'])
 except Exception as exc:atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED_NOT_ACCEPTED',error=str(exc),seconds=time.monotonic()-start,records=records));raise
if __name__=='__main__':main()
