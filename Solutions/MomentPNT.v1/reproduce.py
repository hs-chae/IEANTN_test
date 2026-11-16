"""Public exact source adapter reproduction. No arbitrary application object input."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,time,importlib.util,math
P=Path(__file__).resolve().parent
STD3={'propext','Classical.choice','Quot.sound'}
ROOTS=['MomentPNT.v1.challenge_'+s for s in ['moment_pi','moment_psi','kernel_control_pi','kernel_control_psi','moment_future_pi','moment_prime_rich']]
PUBLIC={'Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Std','Init'}
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
def read(p):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'Duplicate JSON key');out[k]=v
  return out
 def floating(value):
  number=float(value);need(math.isfinite(number),'Nonfinite JSON float');return number
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=floating,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('Nonfinite JSON')))
def save(p,v):
 tmp=p.with_suffix(p.suffix+'.pending');need(not tmp.exists(),'Fresh atomic stage')
 with tmp.open('x')as h:json.dump(v,h,indent=2,allow_nan=False);h.write('\n')
 os.replace(tmp,p)
def load(p,name):
 spec=importlib.util.spec_from_file_location(name,p);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def inputs():
 package=read(P/'SOURCE_PACKAGE_LOCK.json')
 actual_files=[]
 for path in sorted(P.rglob('*')):
  need(not path.is_symlink(),'No source-package symlink')
  if path.is_file():actual_files.append(str(path.relative_to(P)))
 expected_files=sorted([x['path']for x in package['files']]+['SOURCE_PACKAGE_LOCK.json'])
 need(sorted(actual_files)==expected_files,'Exact source-only package file population; use a fresh export')
 for item in package['files']:
  file=P/item['path'];need(file.is_file()and not file.is_symlink()and sha(file)==item['sha256'],'Locked exact package source '+item['path'])
 registry=read(P/'SOURCE_REGISTRY.json');rows={}
 for row in registry['records']:
  path=P/row['path'];need(path.is_file()and not path.is_symlink()and sha(path)==row['sha256'],'Exact materialized source '+row['module'])
  if row['module']in rows and row['parent']!='fresh-core':need(rows[row['module']]['sha256']==row['sha256'],'Source collision')
  rows[row['module']]=row
 for name in ['Solution','MomentPNTDerived']:
  path=P/(name+'.lean');rows[name]={'module':name,'path':name+'.lean','source_root':'.','sha256':sha(path),'parent':'fresh-adapter'}
 scan=load(P/'Dependencies/moment/base/base/base/base/provenance/import_scanner.py','actual_import_scanner')
 for row in rows.values():row['imports']=scan.imports((P/row['path']).read_text())
 def visit(name,seen,order):
  if name in seen:return
  if name not in rows:need(name.split('.')[0]in PUBLIC,'Missing application source '+name);return
  need(not name.endswith('.Challenge'),'Actual solution imports admitted challenge')
  seen.add(name)
  for imp in rows[name]['imports']:visit(imp,seen,order)
  order.append(name)
 order=[];visit('Solution',set(),order)
 return registry,rows,order

def parent_exact(path):
 lock=read(P/'Evidence/PARENT4486_LOCK.json')
 need(sha(path/'RECEIPT.json')==lock['receipt_sha256'],'Exact historical4486 mathematical receipt')
 r=read(path/'RECEIPT.json');need(r['status']=='PASS4486_CHAINED_SOURCE_FIRST_MOMENT_PROGRAMS_TO_STRONGER_PNT'and r['source_modules']==4486,'Actual completed mathematical parent')
 outer=P/'Evidence/parent4486-namespace-receipt.json';probe=P/'Evidence/parent4486-namespace-probe.json'
 need(sha(outer)==lock['outer_receipt_sha256']and sha(probe)==lock['probe_sha256'],'Paired actual isolation attestation')
 q=read(outer);n=read(probe)
 need(q['status']=='PASS_ISOLATED_COMMAND_NOT_MATHEMATICAL_ACCEPTANCE'and n['status']=='PASS_DISTINCT_NAMESPACES_AND_RESTRICTED_PROOF_INPUTS'and n['host_workspace_absent'],'Actual prior namespace gate')
 actual_files=[]
 for entry in sorted(path.rglob('*')):
  need(not entry.is_symlink(),'No parent source/artifact symlink')
  if entry.is_file():actual_files.append(str(entry.relative_to(path)))
 need(actual_files==[x['path']for x in lock['files']],'Exact entire parent file population')
 for row in lock['files']:
  f=path/row['path'];need(f.is_file()and not f.is_symlink()and sha(f)==row['sha256'],'Exact RO source-built parent artifact '+row['path'])
 need(len(list((path/'objects').rglob('*.olean')))==4486,'Exact4486 object population')
 return lock

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--environment',type=Path)
 ap.add_argument('--moment-parent',type=Path);ap.add_argument('--out',type=Path,required=True)
 ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args()
 out=a.out.resolve();need(not out.exists()and not out.is_relative_to(P),'Fresh external owned output')
 registry,rows,order=inputs();out.mkdir(parents=True);logs=out/'logs';logs.mkdir();records=[];began=time.monotonic()
 def run(name,cmd,env=None):
  started=time.monotonic();so=logs/(name+'.stdout');se=logs/(name+'.stderr');tm=logs/(name+'.time')
  with so.open('wb')as f,se.open('wb')as g:q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],cwd=P,env=env,stdout=f,stderr=g)
  record={'name':name,'command':cmd,'exit_code':q.returncode,'seconds':time.monotonic()-started,'stdout_sha256':sha(so),'stderr_sha256':sha(se),'metrics_sha256':sha(tm)}
  records.append(record);save(out/'PROGRESS.json',{'status':'PARTIAL_NOT_ACCEPTED','records':records})
  need(q.returncode==0,'Actual command failed '+name)
  return record
 if a.check_inputs_only:
  save(out/'RECEIPT.json',{'status':'PASS_SOURCE_INPUTS_ONLY_NOT_PROOF_REPLAY','application_closure':len(order),'registry_sha256':sha(P/'SOURCE_REGISTRY.json'),'source_package_lock_sha256':sha(P/'SOURCE_PACKAGE_LOCK.json'),'solution_sha256':sha(P/'Solution.lean'),'roots':ROOTS});return
 need(a.environment is not None,'Explicit portable public generic environment required')
 cap=load(P/'Dependencies/moment/reproduce.py','actual4486_recipe');lock,parent,base,runner=cap.inputs()
 strict_environment=read(a.environment.resolve())
 environment=runner.environment_inputs(a.environment.resolve(),base);need(environment==strict_environment,'Strict environment parsing');compiler=environment['compiler']
 for dependency in environment['generic_dependencies']:
  need(Path(dependency['objects']).resolve().is_relative_to(Path(dependency['source']).resolve()),'Generic object/source path association')
 if a.moment_parent:
  prior=a.moment_parent.resolve();association=parent_exact(prior);kind='VALIDATED_ISOLATED4486_RO_PARENT_PLUS_FRESH_SOURCE_APPEND'
 else:
  prior=out/'fresh4486';run('full4486',[sys.executable,'-I','-B',str(P/'Dependencies/moment/reproduce.py'),'--environment',str(a.environment.resolve()),'--out',str(prior),'--jobs','8'])
  fresh=read(prior/'RECEIPT.json');need(fresh['status']=='PASS4486_CHAINED_SOURCE_FIRST_MOMENT_PROGRAMS_TO_STRONGER_PNT'and fresh['source_lock_sha256']==sha(P/'Dependencies/moment/SOURCE_LOCK.json'),'Fresh same-pipeline source completion')
  association={'fresh_recipe_command':records[-1],'receipt_sha256':sha(prior/'RECEIPT.json')};kind='FRESH_FULL_SOURCE_PARENT_PLUS_APPEND'
 objects=out/'objects';objects.mkdir();expected=out/'expected-objects';expected.mkdir()
 seeds=list((prior/'objects').rglob('*.olean'));need(len(seeds)==4486,'Exact coherent parent overlay')
 for source_object in seeds:
  target=objects/source_object.relative_to(prior/'objects');target.parent.mkdir(parents=True,exist_ok=True)
  target.symlink_to(source_object)
 # Lean selects the first existing top-level namespace directory, so the bank must be coherent.
 env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['LEAN_PATH']=':'.join([str(objects),str(prior/'objects')]+[d['objects']for d in environment['generic_dependencies']])
 old={x['module']:x for x in registry['records']if x['parent']=='4486'}
 compiled=[]
 for module in order:
  row=rows[module]
  if module in old:
   need(old[module]['sha256']==row['sha256'],'Current core/old parent source coherence '+module)
   continue
  src=P/row['path'];obj=objects/Path(module.replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  rec=run('compile-'+module,[compiler,'-j1','-R',str(P/row['source_root']),str(src),'-o',str(obj)],env)
  text=(logs/('compile-'+module+'.stdout')).read_text()+(logs/('compile-'+module+'.stderr')).read_text()
  need("declaration uses 'sorry'"not in text and 'declaration uses `sorry`'not in text,'No admitted actual source')
  rec.update(source_sha256=sha(src),object_sha256=sha(obj));compiled.append(module)
 audit=out/'AuditStd3.lean';audit.write_text('import Solution\nimport Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nrun_elab do\n let env ← getEnv\n for name in (['+','.join('`'+n for n in ROOTS)+'] : List Name) do\n  let some info := env.find? name | throwError "missing {name}"\n  let axioms ← Lean.collectAxioms name\n  logInfo m!"SOLUTION_AUDIT {(Json.mkObj [("name",toJson name.toString),("type_repr",toJson (reprStr info.type)),("axioms",toJson (axioms.toList.map Name.toString))]).compress}"\n')
 run('actual-six-axiom-audit',[compiler,'-j1','-R',str(out),str(audit)],env)
 audits=[json.loads(x.split('SOLUTION_AUDIT ',1)[1])for x in(logs/'actual-six-axiom-audit.stdout').read_text().splitlines()if'SOLUTION_AUDIT 'in x]
 need([x['name']for x in audits]==ROOTS and all(x['type_repr']and set(x['axioms'])<=STD3 for x in audits),'Exact six typed standard closures')
 for actual_object in objects.rglob('*.olean'):
  target=expected/actual_object.relative_to(objects);target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(actual_object)
 challenge='IEANTN.Nodes.MomentPNT.v1.Challenge';row=rows[challenge];dest=expected/Path(challenge.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 run('expected-challenge-template',[compiler,'-j1','-R',str(P/'Core'),str(P/row['path']),'-o',str(dest)],env)
 compareEnv=dict(env);compareEnv['LEAN_PATH']=str(expected)+':'+env['LEAN_PATH']
 run('separate-environment-exact-types',[compiler,'--run',str(P/'AuditExact.lean')],compareEnv)
 exact=[x for x in(logs/'separate-environment-exact-types.stdout').read_text().splitlines()if x.startswith('EXACT_TYPE ')]
 need(exact==['EXACT_TYPE '+n for n in ROOTS],'All six exact Challenge types')
 if a.moment_parent:need(parent_exact(prior)==association,'RO parent unchanged after use')
 save(out/'RECEIPT.json',{'status':'PASS_PUBLIC_SOLUTION_SIX_EXACT_TYPES_STD3','classification':kind,'coherent_validated_RO_parent_overlay_objects':4486,'overlay_kind':'Generated links only to the exact validated source-built RO parent; no additional application input bank','source_cold_append':True,'namespace_isolation':'Separate outer namespace receipt required','parent_association':association,'compiled_modules':compiled,'records':records,'audits':audits,'exact_challenge_types_separate_environment':True,'solution_imports_admitted_challenge':False,'solution_sha256':sha(P/'Solution.lean'),'reproducer_sha256':sha(Path(__file__)),'source_registry_sha256':sha(P/'SOURCE_REGISTRY.json'),'source_package_lock_sha256':sha(P/'SOURCE_PACKAGE_LOCK.json'),'seconds':time.monotonic()-began,'qualification':'Three moment claims consume actual source reads; direct-vector control remains ordinary-kernel verification; derived PrimeRich uses only moment_future_pi. No official Comparator receipt.'})
 print(json.dumps({'status':'PASS_PUBLIC_SOLUTION_SIX_EXACT_TYPES_STD3','new_modules':len(compiled),'roots':len(audits),'seconds':time.monotonic()-began}))
if __name__=='__main__':main()
