#!/usr/bin/env python3
"""Verify completed cold261 evidence, then compile the exact55-source spectral extension.

No historical application or LeanCert object cache is admitted. Only the completed
root's independently source-replayed basis and pinned generic libraries are used.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,math,os,re,resource,subprocess,sys,time
B=Path(__file__).resolve().parent;S=B.parent;N=S.parents[1]
ALLOW={'propext','Classical.choice','Quot.sound'}
def need(c,m):
 if not c:raise ValueError(m)
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
  x=float(s);need(math.isfinite(x),'nonfiniteJSON');return x
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfiniteJSON')))
def save(p,j):
 q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'unexpected pending receipt')
 q.write_text(json.dumps(j,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def audit(s):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",s,re.S)
 need(len(rows)==len({x for x,_ in rows}),'duplicate audit declaration')
 for n,a in rows:need({x.strip()for x in a.split(',')if x.strip()}<=ALLOW,'bad proof axiom:'+n)
 return [{'theorem':n,'axioms':[x.strip()for x in a.split(',')if x.strip()]}for n,a in rows]
def header_imports(text):
 i=0;names=[]
 while i<len(text):
  while i<len(text)and text[i].isspace():i+=1
  if text.startswith('--',i):
   k=text.find('\n',i);i=len(text)if k<0 else k+1;continue
  if text.startswith('/-',i):
   depth=1;i+=2
   while depth and i<len(text):
    if text.startswith('/-',i):depth+=1;i+=2
    elif text.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   need(depth==0,'unterminated import comment');continue
  k=text.find('\n',i);k=len(text)if k<0 else k;line=text[i:k].split('--',1)[0].strip()
  if line=='prelude':i=k+1;continue
  m=re.fullmatch(r'(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.\s]+)',line)
  if not m:break
  names+=m[1].split();i=k+1
 return names

def validate_basis(basis,manifest,m,ctx,resource_proof=None):
 basefile=N/m['basis_manifest'];need(sha(basefile)==m['basis_manifest_sha256'],'basis manifest identity')
 base=read(basefile);need(len(base['modules'])==m['basis_modules']==261,'basis exact261')
 need((basis/'RESULT.json').is_file(),'completed cold261 RESULT not available')
 r=read(basis/'RESULT.json');need(r['status']=='PASS_COLD_ALL_261_SOURCE_MODULES_AND_FINAL_PI_CONSUMERS','basis unfinished/nonpass')
 need(type(r['modules'])is int and r['modules']==261 and r['prebuilt_application_objects_used']is False and r['prebuilt_LeanCert_objects_used']is False,'basis source policy')
 need(sha(basis/'SOURCE_CLOSURE.executed.json')==r['manifest_sha256']==sha(basefile),'basis executed manifest')
 need(sha(basis/'reproduce.executed.py')==r['controller_sha256'],'basis controller copy')
 need(r['compiler_sha256']==ctx['compiler_sha256']==sha(ctx['compiler']),'basis/compiler identity')
 need(sha(basis/'BUILD.json')==r['BUILD_sha256'],'basis BUILD hash')
 build=read(basis/'BUILD.json');need(build['status']=='PASS','basis BUILD status')
 need(len(build['modules'])==261,'basis build count')
 basis_audits=[]
 for want,got in zip(base['modules'],build['modules']):
  mod=want['module'];rel=mod.replace('.','/')
  need(got['module']==mod,'basis module order')
  need(type(got['returncode'])is int and got['returncode']==0,'basis returncode type/status')
  need(sha(N/want['path'])==want['sha256']==got['source_sha256']==sha(basis/'source'/(rel+'.lean')),'basis source:'+mod)
  need(sha(basis/'objects'/(rel+'.olean'))==got['object_sha256'],'basis object:'+mod)
  need(sha(basis/'logs'/(mod+'.stdout'))==got['stdout_sha256']and sha(basis/'logs'/(mod+'.stderr'))==got['stderr_sha256'],'basis log:'+mod)
  basis_audits+=audit((basis/'logs'/(mod+'.stdout')).read_text())
 need(set(base['final_roots'])<={x['theorem']for x in basis_audits},'basis final root audits absent')
 resources=read(S/'pi/RESOURCES.json');need(len(resources['resources'])==1,'exact basis C resource')
 for payload in resources['resources']:
  need(sha(N/payload['path'])==payload['sha256']==sha(basis/'source'/payload['relative_runtime_path']),'basis actual C payload')
 overrides={}
 if r.get('resource_complete_default_recipe')is True:
  need(r['resource_manifest_sha256']==sha(S/'pi/RESOURCES.json'),'resourcecomplete basis manifest')
  need(r['controller_sha256']==sha(S/'scripts/reproduce_pi_complete.py'),'resourcecomplete exact controller')
 else:
  need(resource_proof is not None,'initial two-stage basis requires completed23 resource proof')
  rr=read(resource_proof/'RESULT.json');rb=read(resource_proof/'BUILD.json');selection=read(S/'pi/RESOURCE_CLOSURE.json')
  need(rr['status']=='PASS_EXPLICIT_C_RESOURCE_AND_FRESH23_DEPENDENT_PROOF_REPLAY','resource23 incomplete')
  need(rr['initial_recipe_self_contained']is False and rr['historical_application_cache_used']is False,'resource study identity')
  need(rr['basis_RESULT_sha256']==sha(basis/'RESULT.json')and rr['basis_BUILD_sha256']==sha(basis/'BUILD.json'),'resource23 basis association')
  need(rr['resource_manifest_sha256']==sha(S/'pi/RESOURCES.json')and rr['source_manifest_sha256']==sha(S/'pi/RESOURCE_CLOSURE.json'),'resource23 source/resource manifest')
  need(rr['controller_sha256']==sha(S/'scripts/reproduce_pi_resources.py')and rr['default_complete_controller_sha256']==sha(S/'scripts/reproduce_pi_complete.py'),'resource23 exact controllers')
  need(rr['BUILD_sha256']==sha(resource_proof/'BUILD.json')and rb['status']=='PASS','resource23BUILD')
  need(selection['modules']==base['modules'][238:]and len(rb['modules'])==23,'exact resource-dependent23')
  resource_audits=[]
  for want,got in zip(selection['modules'],rb['modules']):
   mod=want['module'];rel=mod.replace('.','/')
   need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'resource23 compiler status')
   need(sha(resource_proof/'source'/(rel+'.lean'))==want['sha256']==got['source_sha256'],'resource23 source')
   need(sha(resource_proof/'objects'/(rel+'.olean'))==got['object_sha256'],'resource23 object')
   need(sha(resource_proof/'logs'/(mod+'.stdout'))==got['stdout_sha256']and sha(resource_proof/'logs'/(mod+'.stderr'))==got['stderr_sha256'],'resource23 logs')
   resource_audits+=audit((resource_proof/'logs'/(mod+'.stdout')).read_text());overrides[mod]=resource_proof/'objects'/(rel+'.olean')
  need(set(selection['final_roots'])<={x['theorem']for x in resource_audits},'resource23 final audits absent')
  for payload in resources['resources']:need(sha(resource_proof/'source'/payload['relative_runtime_path'])==payload['sha256'],'resource23 C payload')
 names={x['module']for x in base['modules']};done=set(names)
 need(len(m['modules'])==55,'exact append55')
 need(len({x['module']for x in m['modules']})==55,'append distinct identities')
 for row in m['modules']:
  mod=row['module'];p=(N/row['path']).resolve()
  need(mod not in done,'append/basis overlap')
  need(p.is_relative_to(B/'frozen-source') and sha(p)==row['sha256'],'append frozen source:'+mod)
  actual=header_imports(p.read_text());need(actual==row['application_imports']+row['generic_imports'] or set(actual)==set(row['application_imports']+row['generic_imports']),'append import inventory:'+mod)
  need(set(row['application_imports'])<=done,'append topological closure:'+mod)
  need(all(x.split('.')[0]in {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'}for x in row['generic_imports']),'unknown generic import')
  done.add(mod)
 for row in m['resources']:
  need((N/row['path']).resolve().is_relative_to(B/'frozen-source')and sha(N/row['path'])==row['sha256'],'frozen resource')
 return base,r,overrides

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--basis',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--resource-proof',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args();out=a.out.resolve();basis=a.basis.resolve()
 manifest=B/'SOURCE_CLOSURE.json';m=read(manifest)
 ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')))
 ref=read(N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in ref['generic_dependencies']],'generic identity list')
 for dep in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path'],text=True).strip()==dep['revision'],'generic revision')
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=dep['path']).returncode==0,'generic tracked source changed')
 need(ctx['generic_libraries']==[x['library']for x in ctx['generic_dependencies']if x['library_present']],'generic-only object libraries')
 base,basis_receipt,overrides=validate_basis(basis,manifest,m,ctx,a.resource_proof)
 need(not out.exists(),'fresh output required')
 if a.check:print('PASS_COMPLETE_COLD261_BASIS_AND_EXACT55_SOURCE_PREFLIGHT');return
 avail=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'))
 need(avail>=(512+80)*1024**3,'host reserve before admission')
 out.mkdir(parents=True);src=out/'source';obj=out/'objects';logs=out/'logs';union=out/'union'
 for d in[src,obj,logs,union]:d.mkdir()
 # A single joined namespace is needed for RamanujanPV split across basis/new sources.
 for row in base['modules']:
  rel=row['module'].replace('.','/');target=overrides.get(row['module'],basis/'objects'/(rel+'.olean'));link=union/(rel+'.olean')
  link.parent.mkdir(parents=True,exist_ok=True);need(not link.exists(),'basis join collision');link.symlink_to(target.resolve())
 (out/'SOURCE_CLOSURE.executed.json').write_bytes(manifest.read_bytes());(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
 for row in m['resources']:
  rel=(N/row['path']).relative_to(B/'frozen-source');p=src/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((N/row['path']).read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(union),*ctx['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1'
 start=time.monotonic();began=datetime.datetime.now(datetime.timezone.utc).isoformat();rows=[];audits=[]
 try:
  for row in m['modules']:
   mod=row['module'];rel=mod.replace('.','/');f=src/(rel+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((N/row['path']).read_bytes())
   o=obj/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True);cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(o),str(f)]
   t=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,
    preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80<<30,80<<30)))
   stdout=logs/(mod+'.stdout');stderr=logs/(mod+'.stderr');stdout.write_text(cp.stdout);stderr.write_text(cp.stderr)
   match=re.search(r'Maximum resident set size \(kbytes\): (\d+)',cp.stderr);need(match is not None,'missing RSS')
   rr={'module':mod,'source_sha256':sha(f),'returncode':cp.returncode,'seconds':time.monotonic()-t,'command':['/usr/bin/time','-v',*cmd],
    'peak_RSS_KiB':int(match[1]),'memory_cap_bytes':80<<30,'Lean_threads':8,'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),
    'owned_disk_after_bytes':sum(x.stat().st_size for x in out.rglob('*')if x.is_file())}
   if cp.returncode==0:rr['object_sha256']=sha(o)
   rows.append(rr);save(out/'BUILD.json',{'status':'RUNNING'if cp.returncode==0 else'FAIL','modules':rows})
   need(cp.returncode==0,'source compile:'+mod);need(sha(f)==row['sha256']==sha(N/row['path']),'append source changed')
   link=union/(rel+'.olean');link.parent.mkdir(parents=True,exist_ok=True);need(not link.exists(),'new source join collision');link.symlink_to(o.resolve())
   audits+=audit(cp.stdout);print(len(rows),55,mod,round(rr['seconds'],2),flush=True)
  need(set(m['final_roots'])<={x['theorem']for x in audits},'final audits absent')
  need(sha(manifest)==sha(out/'SOURCE_CLOSURE.executed.json'),'manifest changed')
  validate_basis(basis,manifest,m,ctx,a.resource_proof)
  for resource_row in m['resources']:
   rel=(N/resource_row['path']).relative_to(B/'frozen-source')
   need(sha(src/rel)==resource_row['sha256'],'executed C/resource changed')
  for row in rows:
   rel=row['module'].replace('.','/');need(sha(src/(rel+'.lean'))==row['source_sha256']and sha(obj/(rel+'.olean'))==row['object_sha256'],'append source/object changed')
  allowed=[obj.resolve(),(basis/'objects').resolve(),*([(a.resource_proof/'objects').resolve()]if a.resource_proof else[]),*[Path(x).resolve()for x in ctx['generic_libraries']],Path(ctx['compiler']).resolve().parent.parent/'lib/lean'];probes=[]
  for mod in m['roots']:
   f=src/(mod+'.lean');cp=subprocess.run([ctx['compiler'],'--root='+str(src),'--deps',str(f)],cwd=src,env=env,text=True,capture_output=True)
   need(cp.returncode==0,'dependency probe')
   for line in cp.stdout.splitlines():need(any(Path(line.strip()).resolve().is_relative_to(x)for x in allowed),'foreign object dependency')
   probes.append({'module':mod,'dependencies':cp.stdout.splitlines()})
  save(out/'BUILD.json',{'status':'PASS','modules':rows})
  c_run=subprocess.run([sys.executable,str(B/'reproduce_coeff_execution.py'),'--proof-run',str(out),'--out',str(out/'C-execution')],capture_output=True,text=True)
  (out/'C-execution.driver.stdout').write_text(c_run.stdout);(out/'C-execution.driver.stderr').write_text(c_run.stderr)
  need(c_run.returncode==0,'actual coefficient C source execution association')
  result={'schema':'RH_LIMIT_SPECTRAL_COLD_APPEND_V1','status':'PASS_COLD261_PLUS_ALL55_SPECTRAL_SOURCES_AND_ACTUAL_CONSUMERS',
   'began_utc':began,'seconds':time.monotonic()-start,'controller_sha256':sha(__file__),'manifest_sha256':sha(manifest),'compiler_sha256':ctx['compiler_sha256'],
   'resource23_RESULT_sha256':sha(a.resource_proof/'RESULT.json')if a.resource_proof else None,'basis_resource_policy':'Initial261two-stage+explicitfresh23 replay'if a.resource_proof else'complete default261recipe','basis_RESULT_sha256':sha(basis/'RESULT.json'),'basis_BUILD_sha256':sha(basis/'BUILD.json'),'BUILD_sha256':sha(out/'BUILD.json'),
   'coefficient_C_execution_RESULT_sha256':sha(out/'C-execution/RESULT.json'),'basis_modules':261,'append_modules':55,'total_source_modules':316,'axiom_audits':audits,'dependency_probes':probes,
   'peak_child_RSS_KiB':max(x['peak_RSS_KiB']for x in rows),'sampled_peak_owned_disk_bytes':max(x['owned_disk_after_bytes']for x in rows),
   'observed_process_OOM_events':0,'OOM_evidence':'all316basis+appendacceptedcompilerprocessesreturned0; hostglobalOOMnotattributed',
   'python_optimization':sys.flags.optimize,'historical_application_or_LeanCert_objects_used':False,'namespace_join':'Single symlink namespace over validatedfresh261basis plus55freshoutputs; eachsource/objectsha checked',
   'source_first_PV':'Only reused actualCcoefficient component; allnew numerical enclosures kernel-only; RH/sourceinputs explicit'}
  save(out/'RESULT.json',result);print(result['status'],flush=True)
 except BaseException as ex:
  save(out/'FAILURE.json',{'status':'FAIL','error':str(ex),'elapsed_seconds':time.monotonic()-start,'completed_modules':len(rows)});raise
if __name__=='__main__':main()
