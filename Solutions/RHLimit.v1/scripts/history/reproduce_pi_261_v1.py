#!/usr/bin/env python3
"""Cold source-only replay of both actual ordinary-pi consumers (261 modules).

Only the exact pinned compiler and generic dependency libraries may be reused.
No application or LeanCert object cache is accepted. Numeric C execution is
reproduced separately by analytic/reproduce.py and joined by source hashes.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,math,os,re,resource,subprocess,sys,time
S=Path(__file__).resolve().parents[1];N=S.parents[1]
ALLOW={'propext','Classical.choice','Quot.sound'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
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
  x=float(s);need(math.isfinite(x),'nonfinite JSON');return x
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,
   parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def save(p,j):
 q=p.with_name('.'+p.name+'.pending');need(not q.exists(),'unexpected pending receipt')
 q.write_text(json.dumps(j,indent=2,allow_nan=False)+'\n');os.replace(q,p)
def axiom_audit(output):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S)
 need(len(rows)==len({n for n,_ in rows}),'duplicate axiom declaration')
 for n,v in rows:need({x.strip()for x in v.split(',')if x.strip()}<=ALLOW,'unaccepted axiom:'+n)
 return [{'theorem':n,'axioms':[x.strip()for x in v.split(',')if x.strip()]}for n,v in rows]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True)
 p.add_argument('--check',action='store_true');a=p.parse_args();out=a.out.resolve()
 manifest=S/'pi/SOURCE_CLOSURE.json';m=read(manifest);need(len(m['modules'])==261,'exact source closure size')
 names=[r['module']for r in m['modules']];need(len(set(names))==len(names),'duplicate module identities')
 done=set()
 for r in m['modules']:
  f=(N/r['path']).resolve();need(f.is_relative_to(S),'standalone selected source scope')
  need(sha(f)==r['sha256'],'source changed:'+r['module'])
  need(set(r['application_imports'])<=done,'source order/closure incomplete:'+r['module']);done.add(r['module'])
 context=Path(os.environ.get('IEANTN_GENERIC_CONTEXT',N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'))
 ctx=read(context);reference=read(N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 need(ctx['compiler_sha256']==reference['compiler_sha256']==sha(ctx['compiler']),'compiler identity')
 need([(d['name'],d['revision'])for d in ctx['generic_dependencies']]==[(d['name'],d['revision'])for d in reference['generic_dependencies']],'generic source identities')
 for d in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic source revision:'+d['name'])
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'generic tracked source changed:'+d['name'])
 need(ctx['generic_libraries']==[d['library']for d in ctx['generic_dependencies']if d['library_present']],'generic-only library paths')
 need(not out.exists(),'fresh output required')
 if a.check:print('PASS_PI_COMPLETE_SOURCE_AND_DEPENDENCY_PREFLIGHT_ONLY');return
 avail=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'))
 need(avail>=(512+48)*1024**3,'host reserve before admission')
 out.mkdir(parents=True);src=out/'source';obj=out/'objects';logs=out/'logs'
 for f in[src,obj,logs]:f.mkdir()
 (out/'SOURCE_CLOSURE.executed.json').write_bytes(manifest.read_bytes());(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(obj),*ctx['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1'
 rows=[];audits=[];start=time.monotonic();began=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  for r in m['modules']:
   mod=r['module'];relative=mod.replace('.','/');f=src/(relative+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((N/r['path']).read_bytes())
   o=obj/(relative+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
   command=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(o),str(f)]
   before=time.monotonic();run=subprocess.run(['/usr/bin/time','-v',*command],cwd=src,env=env,text=True,capture_output=True,
     preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(48*1024**3,48*1024**3)))
   stdout=logs/(mod+'.stdout');stderr=logs/(mod+'.stderr');stdout.write_text(run.stdout);stderr.write_text(run.stderr)
   rr={'module':mod,'source_sha256':sha(f),'returncode':run.returncode,'seconds':time.monotonic()-before,'command':['/usr/bin/time','-v',*command],
       'memory_cap_bytes':48*1024**3,'Lean_threads':8,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr).group(1)),
       'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'owned_disk_after_bytes':sum(x.stat().st_size for x in out.rglob('*')if x.is_file())}
   if run.returncode==0:rr['object_sha256']=sha(o)
   rows.append(rr);save(out/'BUILD.json',{'status':'RUNNING'if run.returncode==0 else'FAIL','modules':rows})
   need(run.returncode==0,'source compile failed:'+mod);need(sha(N/r['path'])==r['sha256']==sha(f),'source changed during replay:'+mod)
   audits+=axiom_audit(run.stdout)
   print(len(rows),len(names),mod,round(rr['seconds'],2),flush=True)
  need(len(rows)==len(names),'incomplete source replay');need(sha(manifest)==sha(out/'SOURCE_CLOSURE.executed.json'),'manifest changed')
  roots={r['theorem']for r in audits};need(set(m['final_roots'])<=roots,'missing final theorem axiom audit')
  for row in rows:
   relative=row['module'].replace('.','/');need(sha(src/(relative+'.lean'))==row['source_sha256']and sha(obj/(relative+'.olean'))==row['object_sha256'],'source/object changed')
  allowed=[obj.resolve(),*[Path(x).resolve()for x in ctx['generic_libraries']],Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
  probes=[]
  for mod in m['roots']:
   f=src/(mod+'.lean');run=subprocess.run([ctx['compiler'],'--root='+str(src),'--deps',str(f)],cwd=src,env=env,text=True,capture_output=True)
   need(run.returncode==0,'dependency probe failed:'+mod)
   for line in run.stdout.splitlines():
    d=Path(line.strip()).resolve();need(any(d.is_relative_to(x)for x in allowed),'undeclared object:'+str(d))
   probes.append({'module':mod,'dependencies':run.stdout.splitlines()})
  save(out/'BUILD.json',{'status':'PASS','modules':rows})
  result={'schema':'RH_LIMIT_ACTUAL_PI_SOURCE_REPLAY_V1','status':'PASS_COLD_ALL_261_SOURCE_MODULES_AND_FINAL_PI_CONSUMERS','began_utc':began,'seconds':time.monotonic()-start,'compiler_sha256':ctx['compiler_sha256'],'controller_sha256':sha(__file__),'manifest_sha256':sha(manifest),'python_optimization':sys.flags.optimize,'modules':len(rows),'prebuilt_application_objects_used':False,'prebuilt_LeanCert_objects_used':False,'axiom_audits':audits,'dependency_probes':probes,'BUILD_sha256':sha(out/'BUILD.json'),'peak_child_RSS_KiB':max(r['peak_RSS_KiB']for r in rows),'sampled_peak_owned_disk_bytes':max(r['owned_disk_after_bytes']for r in rows),'disk_sampling':'after each module; brief intra-module peaks not independently measured','observed_process_OOM_events':0,'OOM_evidence':'all261 accepted compiler processes returned0; global host OOM counter not attributed','analytic_source_assumptions_preserved':True,'whole_pipeline_source_first_PV':False,'source_first_PV_component':m['source_first_PV_scope']}
  save(out/'RESULT.json',result);print(result['status'],flush=True)
 except BaseException as ex:
  save(out/'FAILURE.json',{'status':'FAIL','error':str(ex),'elapsed_seconds':time.monotonic()-start,'completed_modules':len(rows)});raise
if __name__=='__main__':main()
