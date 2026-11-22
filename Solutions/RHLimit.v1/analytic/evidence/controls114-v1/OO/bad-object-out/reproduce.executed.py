#!/usr/bin/env python3
"""Cold113 source replay (default) or hash-bound fresh113 bank, then actual absolute-octic bridge."""
from pathlib import Path
import argparse,hashlib,json,math,os,re,resource,subprocess,sys,time
B=Path(__file__).resolve().parent;N=B.parents[2];OLD=N/'Solutions/RHContinuation.v1'
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
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
 q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'stale pending file')
 q.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def audit(s,names):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",s,re.S)
 need(len(rows)==len(set(n for n,_ in rows))==len(names),'audit cardinality')
 need(set(n for n,_ in rows)==set(names),'audit identity')
 for n,v in rows:need({x.strip()for x in v.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'},'unexpected axiom:'+n)
 return [{'theorem':n,'axioms':[x.strip()for x in v.split(',')if x.strip()]}for n,v in rows]
def validate_base(base):
 r=read(base/'RESULT.json');need(r['schema']=='RH_LIMIT_COLD113_ANALYTIC_V1'and r['status']=='PASS_COMPLETE_SAME_SOURCE111_PLUS_EXACT_ANALYTIC_BRIDGES','complete source-only113 bank required')
 need(r['original_modules']==111 and r['new_modules']==2 and r['no_prebuilt_application_objects']is True,'complete original/new scope')
 need(r['compiler_sha256']==COMPILER_SHA,'base compiler')
 need(r['manifest_sha256']==sha(B/'ANALYTIC_MANIFEST.json'),'base analytic manifest identity')
 need(r['controller_sha256']==sha(B/'reproduce_common.py')==sha(base/'reproduce.executed.py'),'base executed controller identity')
 need(r['BUILD_sha256']==sha(base/'BUILD.json'),'base source/object binding identity')
 build=read(base/'BUILD.json');need(build['status']=='PASS'and len(build['modules'])==113,'complete113 builds')
 expect=[(x['module'],x['sha256'])for x in read(OLD/'integration/SOURCE_CLOSURE.json')['modules']]+[(x['module'],x['sha256'])for x in read(B/'ANALYTIC_MANIFEST.json')['new_modules']]
 for row,(mod,pin)in zip(build['modules'],expect):
  need(row['module']==mod and type(row['returncode'])is int and row['returncode']==0,'base executed module identity')
  rel=mod.replace('.','/');src=base/'source'/(rel+'.lean');obj=base/'objects'/(rel+'.olean')
  need(src.is_file()and obj.is_file()and not src.is_symlink()and not obj.is_symlink(),'base source/object files')
  need(row['source_sha256']==pin==sha(src)and row['object_sha256']==sha(obj),'base source/object bytes')
 return build['modules']
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh output required');manifest=read(B/'ABSOLUTE_MANIFEST.json')
 need(sha(B/'reproduce_common.py')==manifest['common_controller_sha256']and sha(B/'ANALYTIC_MANIFEST.json')==manifest['common_manifest_sha256'],'common source route identity')
 source=B/'AbsoluteStieltjes.lean';need(sha(source)==manifest['source_sha256'],'actual absolute bridge source identity')
 env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None)
 if a.check:
  subprocess.run([sys.executable,str(B/'reproduce_common.py'),'--out',str(out),'--check'],env=env,check=True);print('PASS_ABSOLUTE_SOURCE_PREFLIGHT_ONLY');return
 out.mkdir(parents=True);start=time.monotonic();base=a.base_run.resolve()if a.base_run else out/'base'
 (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes());(out/'ABSOLUTE_MANIFEST.executed.json').write_bytes((B/'ABSOLUTE_MANIFEST.json').read_bytes())
 if a.base_run is None:
  cmd=[sys.executable,str(B/'reproduce_common.py'),'--out',str(base)]
  with(out/'base.stdout').open('w')as so,(out/'base.stderr').open('w')as se:r=subprocess.run(cmd,env=env,stdout=so,stderr=se)
  need(r.returncode==0,'fresh common source replay failed')
 rows=validate_base(base);ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',OLD/'scripts/GENERIC_CONTEXT.json')))
 need(ctx['compiler_sha256']==COMPILER_SHA==sha(ctx['compiler']),'compiler identity')
 ref=read(OLD/'scripts/GENERIC_CONTEXT.json')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in ref['generic_dependencies']],'generic source pins')
 for d in ctx['generic_dependencies']:need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic revision:'+d['name'])
 src=out/'source';obj=out/'objects';logs=out/'logs';src.mkdir();obj.mkdir();logs.mkdir();target=src/'AbsoluteStieltjes.lean';target.write_bytes(source.read_bytes())
 env['LEAN_PATH']=':'.join([str(obj),str(base/'objects'),*ctx['generic_libraries']]);cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(obj/'AbsoluteStieltjes.olean'),str(target)];before=time.monotonic()
 r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
 (logs/'AbsoluteStieltjes.stdout').write_text(r.stdout);(logs/'AbsoluteStieltjes.stderr').write_text(r.stderr);need(r.returncode==0,'actual absolute bridge compilation failed');aa=audit(r.stdout,manifest['audits'])
 need(sha(target)==sha(source)==manifest['source_sha256'],'source changed during run');validate_base(base)
 result={'schema':'RH_LIMIT_COLD114_ABSOLUTE_STIELTJES_V1','status':'PASS_SOURCE_LINKED_ACTUAL_OCTIC_ABSOLUTE_STIELTJES','seconds':time.monotonic()-start,'module_seconds':time.monotonic()-before,'source_modules':114,'fresh_base':a.base_run is None,'base':str(base),'base_result_sha256':sha(base/'RESULT.json'),'base_BUILD_sha256':sha(base/'BUILD.json'),'controller_sha256':sha(__file__),'manifest_sha256':sha(B/'ABSOLUTE_MANIFEST.json'),'source_sha256':sha(target),'object_sha256':sha(obj/'AbsoluteStieltjes.olean'),'compiler_sha256':COMPILER_SHA,'command':['/usr/bin/time','-v',*cmd],'axiom_audits':aa,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',r.stderr).group(1)),'max_child_RSS_KiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'python_optimization':sys.flags.optimize,'final_owned_bytes':sum(f.stat().st_size for f in out.rglob('*')if f.is_file()),'OOM':'accepted compiler returned0; kernel OOM counter not independently sampled','source_first_PV':False,'published_BPT_input_proved':False,'numerical_moment_caps_proved':False,'infinite_zero_tail_proved':False,'smoothed_explicit_formula_proved':False}
 save(out/'RESULT.json',result);print(result['status'])
if __name__=='__main__':main()
