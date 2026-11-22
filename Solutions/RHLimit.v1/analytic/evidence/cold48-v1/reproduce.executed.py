#!/usr/bin/env python3
"""Fresh46-source C-log proof plus unconditional Stieltjes and reduced actual-PNT consumer.

The actual old C source is unchanged. This script does not call kernel arithmetic
source-first PV: only the reused documented C execution-to-consumer chain has that tier.
"""
from pathlib import Path
import argparse,hashlib,json,math,os,re,resource,subprocess,sys,time
B=Path(__file__).resolve().parent;N=B.parents[2]
OLD=N/'Solutions/RHContinuation.v1';COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(s):
  v=float(s);need(math.isfinite(v),'nonfinite JSON');return v
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,
   parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def save(p,d):
 q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'unexpected pending file')
 q.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def audit(text,expected):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
 need(len(rows)==len({x[0]for x in rows})==len(expected),'audit cardinality')
 need({x[0]for x in rows}==set(expected),'audit declaration identities')
 for name,s in rows:need({x.strip()for x in s.split(',')if x.strip()}<=ALLOWED,'nonstandard axiom:'+name)
 return [{'theorem':n,'axioms':[x.strip()for x in s.split(',')if x.strip()]}for n,s in rows]
def bank(base,own):
 r=read(base/'RESULT.json');need(r['status']=='PASS'and r['application_source_modules']==46,'complete original46-source replay')
 need(r['no_prebuilt_application_objects']is True,'prebuilt baseline')
 closure=read(base/'FROZEN_SOURCE_CLOSURE.json');build=read(base/'BUILD.json')
 need(build['status']=='PASS'and len(closure)==len(build['modules'])==46,'complete source/build association')
 records=[]
 for src,row in zip(closure,build['modules']):
  mod=src['module'];need(row['module']==mod and type(row['returncode'])is int and row['returncode']==0,'baseline compile route')
  f=base/'frozen-source'/(mod.replace('.','/')+'.lean');obj=base/'objects'/(mod.replace('.','/')+'.olean')
  need(src['sha256']==row['source_sha256']==sha(f),'baseline frozen source identity')
  need(obj.is_file()and not obj.is_symlink(),'baseline object')
  records.append({'module':mod,'source_sha256':sha(f),'object_sha256':sha(obj),'bytes':obj.stat().st_size})
 if own:
  prior=read(base/'RH_LIMIT_BASE_BINDING.json');need(prior['files']==records,'baseline object or source changed')
 else:save(base/'RH_LIMIT_BASE_BINDING.json',{'files':records,'source_controller_sha256':sha(OLD/'parabolic/reproduce_clog.py')})
 return records

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True)
 p.add_argument('--base-run',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args()
 out=a.out.resolve();need(not out.exists(),'fresh output required');m=read(B/'SOURCE_MANIFEST.json')
 for row in m['files']:need(sha(B/row['path'])==row['sha256'],'owned source pin:'+row['path'])
 need(sha(OLD/'parabolic/reproduce_clog.py')==m['baseline_reproducer_sha256'],'old source replayer changed')
 reference=read(OLD/'scripts/GENERIC_CONTEXT.json');cp=Path(os.environ.get('IEANTN_GENERIC_CONTEXT',OLD/'scripts/GENERIC_CONTEXT.json'));ctx=read(cp)
 need(ctx['compiler_sha256']==COMPILER_SHA==sha(ctx['compiler']),'compiler identity')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in reference['generic_dependencies']],'generic source pins')
 for dep in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path'],text=True).strip()==dep['revision'],'generic revision:'+dep['name'])
 if a.check:print('PASS_SOURCE_COMPILER_DEPENDENCY_PREFLIGHT_ONLY');return
 out.mkdir(parents=True);start=time.monotonic();env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None)
 base=a.base_run.resolve()if a.base_run else out/'baseline'
 if a.base_run is None:
  cmd=[sys.executable,str(OLD/'parabolic/reproduce_clog.py'),'--out',str(base)]
  with(out/'baseline.stdout').open('w')as so,(out/'baseline.stderr').open('w')as se:r=subprocess.run(cmd,env=env,stdout=so,stderr=se)
  need(r.returncode==0,'fresh original46-source replay failed; preserve partial evidence')
 records=bank(base,a.base_run is not None)
 src=out/'source';src.mkdir();objdir=out/'objects';objdir.mkdir();logs=out/'logs';logs.mkdir()
 env['LEAN_PATH']=':'.join([str(objdir),str(base/'objects'),*ctx['generic_libraries']]);rows=[]
 for row in m['files']:
  mod=row['module'];target=src/row['path'];target.write_bytes((B/row['path']).read_bytes())
  cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(objdir/(mod+'.olean')),str(target)]
  st=time.monotonic();r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,
    preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
  (logs/(mod+'.stdout')).write_text(r.stdout);(logs/(mod+'.stderr')).write_text(r.stderr)
  need(r.returncode==0,'new formal source failed:'+mod);aa=audit(r.stdout,row['audits'])
  rows.append({'module':mod,'source_sha256':sha(target),'object_sha256':sha(objdir/(mod+'.olean')),'seconds':time.monotonic()-st,'command':cmd,'axiom_audits':aa})
  print('PASS',mod,flush=True)
 for record in records:need(sha(base/'objects'/(record['module'].replace('.','/')+'.olean'))==record['object_sha256'],'baseline object changed during build')
 for row in m['files']:need(sha(B/row['path'])==row['sha256'],'owned source changed during build')
 result={'schema':'RH_LIMIT_UNCONDITIONAL_STIELTJES_SOURCE_LINKED_PNT_V1','status':'PASS_ACTUAL_STIELTJES_CLOSURE_AND_SOURCE_LINKED_FOUR_INPUT_PNT','seconds':time.monotonic()-start,'python_optimization':sys.flags.optimize,'controller_sha256':sha(__file__),'manifest_sha256':sha(B/'SOURCE_MANIFEST.json'),'baseline':str(base),'baseline_result_sha256':sha(base/'RESULT.json'),'baseline_object_binding_sha256':sha(base/'RH_LIMIT_BASE_BINDING.json'),'fresh_baseline_rebuilt':a.base_run is None,'source_modules':48,'new_modules':rows,'compiler_sha256':COMPILER_SHA,'max_child_RSS_KiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'new_kernel_OOM_counter':'not independently sampled; every accepted child returned0','remaining_analytic_inputs':['RHSmoothingInputs.v1.box_explicit_formula','RHSmoothingInputs.v1.box_zero_estimate','BoxMellinInputs.v1.first_moment','BoxMellinInputs.v1.second_moment_identity'],'RH_explicit':True,'numeric_moment_or_Stieltjes_premise':False,'source_first_PV_component':'Unchanged actual verified_finite_log.c→AST/execution→127word bounds→kernel moment aggregation→actual box_psi; Stieltjes closure is ordinary kernel analysis, not PV.','whole_pipeline_source_first_PV':False,'official_Comparator_receipt':False}
 save(out/'RESULT.json',result);print(result['status'],flush=True)
if __name__=='__main__':main()
