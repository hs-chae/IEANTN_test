"""Exact source-only565+3 stronger fixed-vector kernel checker continuation."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,math,os,shutil,subprocess,sys,time
B=Path(__file__).resolve().parent;STD3={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON');d[k]=v
  return d
 def bad(s):raise ValueError('nonfiniteJSON')
 def floating(s):
  v=float(s);need(math.isfinite(v),'overflowJSON');return v
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def strict(p):return parse(p.read_text())
def atomic(p,v):
 q=p.with_suffix('.pending');q.write_text(json.dumps(v,indent=2)+'\n');q.replace(p)
def inputs():
 lock=strict(B/'SOURCE_LOCK.json');spec=importlib.util.spec_from_file_location('pure565',B/'base/reproduce.py');parent=importlib.util.module_from_spec(spec);spec.loader.exec_module(parent);base=parent.inputs();need(sha(B/'base/SOURCE_LOCK.json')==lock['base_source_lock_sha256'],'same565sourceparent');rows=lock['sources'];need(len(rows)==3 and len({r['module']for r in rows})==3 and len({r['path']for r in rows})==3 and len(lock['roots'])==len(set(lock['roots']))==17 and lock['root_modules']==[r['module']for r in rows],'unique3sources/17roots')
 need([r['module']for r in rows]==['SynergyVector300.Model','SynergyVector300.Data','SynergyVector300.Real'],'exact3module build order')
 allowed={r['module']for r in base['sources']}|{r['module']for r in rows};public=('Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Std','Init')
 import re
 printed=[];namespace=None
 for row in rows:
  need(Path(row['path'])==Path('source')/Path(row['module'].replace('.','/')).with_suffix('.lean'),'canonical source/module path')
  for line in(B/row['path']).read_text().splitlines():
   found=re.match(r'^(?:public )?import\s+(.+)',line)
   if found:need(all(n in allowed or n.split('.')[0]in public for n in found.group(1).split('--')[0].split()),'known actual import edges')
   ns=re.match(r'^namespace\s+([\w.]+)',line)
   if ns:namespace=ns.group(1)
   if line.startswith('#print axioms '):
    need(namespace is not None,'written namespace for each root');printed.append(namespace+'.'+line.split()[-1])
 need(printed==lock['roots'],'exact written17root identities')
 inventory=strict(B/lock['written_root_inventory']);need(sha(B/lock['written_root_inventory'])==lock['written_root_inventory_sha256']and len(inventory['rows'])==17 and[r['declaration']for r in inventory['rows']]==lock['roots']and len({(r['file'],r['line'],r['declaration'])for r in inventory['rows']})==17,'exact17written identities')
 for row in inventory['rows']:
  source=B/row['file'];lines=source.read_text().splitlines();warm=strict(B/row['accepted_warm_receipt']);need(sha(source)==row['source_sha256']==warm['source_sha256']and sha(B/row['accepted_warm_receipt'])==row['accepted_warm_receipt_sha256'],'exact accepted perfile source/receipt')
  need(lines[row['line']-1].startswith('theorem '+row['declaration'].split('.')[-1])and lines[row['print_line']-1]=='#print axioms '+row['declaration'].split('.')[-1]and row['declaration']in warm['roots']and warm['audits'][row['declaration']]==row['accepted_full_axioms'],'actual writtenline/compilerqualifiedidentity')
 for row in rows+strict(B/'REPRODUCER_LOCK.json')['files']:
  rel=Path(row['path']);p=B/rel;need(not rel.is_absolute()and'..'not in rel.parts and p.is_file()and not p.is_symlink()and sha(p)==row['sha256']and p.stat().st_size==row['bytes'],'exact source/reproducer input '+str(rel))
 need(not list(B.rglob('*.olean'))and not list(B.rglob('*.pyc')),'no application objects/caches in capsule');return lock,base

def prior(run,base,environment,require_fixed):
 top=strict(run/'RECEIPT.json');proof=run/'proof';p=strict(proof/'RECEIPT.json');need(top['status']=='PASS565_FRESH_PURE_MOMENT_NUMERICS_AND_FULL_ANT_SOURCE_GRAPH'and top['application_object_inputs']==[]and top['source_modules']==565 and top['typed_standard_roots']==1124 and p['status']=='PASS_PURE_MOMENT_PNT_SOURCE_COLD_EMPTY_BANK','actual source-fresh565only')
 if require_fixed:need(sha(run/'RECEIPT.json')==strict(B/'SOURCE_LOCK.json')['accepted_prior565_receipt_sha256'],'exact independently accepted565 receipt')
 for key,path in [('source_lock_sha256',B/'base/SOURCE_LOCK.json'),('reproducer_sha256',B/'base/reproduce.py'),('reproducer_lock_sha256',B/'base/REPRODUCER_LOCK.json'),('proof_receipt_sha256',proof/'RECEIPT.json'),('numerical_receipt_sha256',run/'numerics/RECEIPT.json'),('cleanup_receipt_sha256',run/'CLEANUP.json')]:need(top[key]==sha(path),'exact prior565 '+key)
 cc=environment['compiler'];byname={r['name']:r for r in p['records']};names={r['module']for r in base['sources']};need(len(byname)==len(p['records'])==566 and set(byname)==names|{'audit'},'exact565prior source/execution population');objects=[];vi=None;vo=None
 for row in base['sources']:
  rec=byname[row['module']];cmd=rec['command'];rel=Path(row['module'].replace('.','/')).with_suffix('.olean');obj=proof/'objects'/rel
  need(len(cmd)==7 and cmd[:3]==[cc,'-j1','-R']and cmd[5]=='-o','pinned source compiler')
  inp=Path(cmd[3]).parent;outp=Path(cmd[6]);suffix=Path('objects')/rel;need(str(outp).endswith('/'+str(suffix)),'canonical object command');root=Path(str(outp)[:-len('/'+str(suffix))])
  if vi is None:vi,vo=inp,root
  need((inp,root)==(vi,vo)and Path(cmd[4])==vi/row['path']and cmd[3]==str(vi/'source'),'same recorded source/output trees')
  need(rec['object_sha256']==sha(obj)and sha(B/'base'/row['path'])==row['sha256'],'exact source-built object');objects.append(dict(module=row['module'],object_sha256=sha(obj)))
 need(byname['audit']['command']==[cc,'-j1','-R',str(vo),str(vo/'Audit.lean')],'exact prior audit compiler/command')
 for rec in p['records']:
  need(rec['exit_code']==0,'actual prior child exit')
  for suffix,k in[('.stdout','stdout_sha256'),('.stderr','stderr_sha256'),('.time','time_sha256')]:need(sha(proof/'logs'/(rec['name']+suffix))==rec[k],'actual prior log')
 actual=[parse(s.split('BODY_AUDIT ',1)[1])for s in(proof/'logs/audit.stdout').read_text().splitlines()if'BODY_AUDIT 'in s];need(actual==p['audits']and[x['name']for x in actual]==base['roots']and len(actual)==1124 and all(x['type_repr']and set(x['axioms'])<=STD3 for x in actual),'all1124 actual typed Std3 prior roots')
 need({str(q.relative_to(proof/'objects'))for q in(proof/'objects').rglob('*.olean')}=={str(Path(n.replace('.','/')).with_suffix('.olean'))for n in names},'exact565prior objects')
 return dict(prior_receipt_sha256=sha(run/'RECEIPT.json'),proof_receipt_sha256=sha(proof/'RECEIPT.json'),objects=objects,recorded_virtual_input=str(vi),recorded_virtual_output=str(vo))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--environment',type=Path);ap.add_argument('--base-run',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args();lock,base=inputs();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh external output');out.mkdir(parents=True);flags=[]if sys.flags.optimize==0 else['-O'if sys.flags.optimize==1 else'-OO'];start=time.monotonic();logs=out/'logs';logs.mkdir();records=[]
 def execute(name,command,env=None):
  t=time.monotonic();so=logs/(name+'.stdout');se=logs/(name+'.stderr');tm=logs/(name+'.time')
  with so.open('wb')as f,se.open('wb')as g:q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*command],cwd=B,env=env,stdout=f,stderr=g)
  r=dict(name=name,command=command,exit_code=q.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(so),stderr_sha256=sha(se),time_sha256=sha(tm));records.append(r);need(q.returncode==0,'actual child '+name);need(not any(s in so.read_text()+se.read_text()for s in['sorryAx','Lean.ofReduceBool',"declaration uses 'sorry'",'declaration uses `sorry`']),'unproved/native diagnostic');return r
 execute('proposal-regeneration',[sys.executable,'-B',*flags,str(B/'regenerate_proposal.py'),'--out',str(out/'proposal')]);need(sha(out/'proposal/Data.lean')==next(r['sha256']for r in lock['sources']if r['module']=='SynergyVector300.Data'),'exact regenerated kernel proposal source')
 if a.check_inputs_only:atomic(out/'RECEIPT.json',dict(status='PASS568_EXACT_SOURCES_AND_REGENERATED_PROPOSAL_ONLY_NOT_REPLAY',source_modules=568,records=records));return
 need(a.environment is not None and a.environment.is_file(),'pinned environment');environment=strict(a.environment);cc=environment['compiler'];tool=Path(cc).parent.parent
 for pin in base['runtime_pins']['toolchain_files']:need(sha(tool/pin['path'])==pin['sha256'],'exact compiler/kernel/runtime')
 need([{k:d[k]for k in['name','commit','url']}for d in environment['generic_dependencies']]==base['generic_dependencies'],'exact generic environment')
 for d in environment['generic_dependencies']:need(subprocess.run(['git','-C',d['source'],'rev-parse','HEAD'],check=True,capture_output=True,text=True).stdout.strip()==d['commit'],'pinned generic commit')
 try:
  run=a.base_run.resolve()if a.base_run else out/'fresh565'
  if a.base_run is None:execute('full565',[sys.executable,'-B',*flags,str(B/'base/reproduce.py'),'--environment',str(a.environment.resolve()),'--out',str(run),'--jobs','8'])
  association=prior(run,base,environment,a.base_run is not None);atomic(out/'PRIOR_BEFORE.json',association);bank=out/'objects';bank.mkdir()
  for row in association['objects']:
   rel=Path(row['module'].replace('.','/')).with_suffix('.olean');p=bank/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(run/'proof/objects'/rel,p);need(sha(p)==row['object_sha256'],'same565source-built seed')
  env=dict(os.environ,LEAN_PATH=':'.join([str(bank)]+[d['objects']for d in environment['generic_dependencies']]),LEAN_NUM_THREADS='1')
  for row in lock['sources']:
   p=B/row['path'];obj=bank/Path(row['module'].replace('.','/')).with_suffix('.olean');need(not obj.exists(),'no module shadowing');obj.parent.mkdir(parents=True,exist_ok=True);rec=execute(row['module'],[cc,'-j1','-R',str(B/'source'),str(p),'-o',str(obj)],env);rec.update(source_sha256=sha(p),object_sha256=sha(obj))
  audit=out/'Audit.lean';audit.write_text(''.join('import '+n+'\n'for n in lock['root_modules'])+'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nrun_elab do\n let env ← getEnv\n for n in (['+','.join('`'+n for n in lock['roots'])+'] : List Name) do\n  let some ci := env.find? n | throwError "missing {n}"\n  let ax ← Lean.collectAxioms n\n  logInfo m!"VECTOR_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n');execute('audit',[cc,'-j1','-R',str(out),str(audit)],env);audits=[parse(s.split('VECTOR_AUDIT ',1)[1])for s in(logs/'audit.stdout').read_text().splitlines()if'VECTOR_AUDIT 'in s];need([r['name']for r in audits]==lock['roots']and all(isinstance(r.get('type_repr'),str) and r['type_repr'] and set(r['axioms'])<=STD3 for r in audits),'all17actual typed Std3 roots')
  need(len(list(bank.rglob('*.olean')))==568,'exact568objects');after=prior(run,base,environment,a.base_run is not None);need(after==association,'full prior association unchanged');atomic(out/'PRIOR_AFTER.json',after);inputs()
 except Exception as ex:atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED',error=str(ex),records=records));raise
 atomic(out/'RECEIPT.json',dict(status='PASS568_CHAINED565_PLUS3_KERNEL_VECTOR_STRONGER_PNT',source_modules=568,new_sources=3,new_typed_std3_roots=17,analytic_inputs=14,coefficient='0.008732871',onset='exp(300)',source_first_PV=False,records=records,audits=audits,seconds=time.monotonic()-start,source_lock_sha256=sha(B/'SOURCE_LOCK.json'),reproducer_sha256=sha(Path(__file__)),reproducer_lock_sha256=sha(B/'REPRODUCER_LOCK.json'),same_pipeline_source_built_object_inputs=565,qualification='Validated565same-pipeline source-built bank plus3new pure source compiles. Notempty-bank568; full-clean565+3 route provided. Ordinarykernel checking,NOTsource-firstPV; stronger than two-moment summary, unchanged14premises. No globalbest/optimality or exclusivePVgain. Namespace/resource acceptance separate.'))
if __name__=='__main__':main()
