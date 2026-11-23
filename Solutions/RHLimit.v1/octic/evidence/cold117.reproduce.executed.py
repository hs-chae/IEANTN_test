#!/usr/bin/env python3
"""Cold, bounded same-source111-module graph plus four closed octic contracts and final consumers."""
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
def audit(s,expected):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",s,re.S)
 need(len(rows)==len(set(n for n,_ in rows))==len(expected),'audit cardinality')
 need(set(n for n,_ in rows)==set(expected),'audit identity')
 for n,v in rows:need({x.strip()for x in v.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'},'unexpected axiom:'+n)
 return [{'theorem':n,'axioms':[x.strip()for x in v.split(',')if x.strip()]}for n,v in rows]
def self_test():
 import tempfile
 with tempfile.TemporaryDirectory(prefix='octic-validator-')as td:
  p=Path(td)/'input.json'
  for raw in ['{"x":1,"x":2}','NaN','Infinity','1e999']:
   p.write_text(raw)
   try:read(p)
   except (ValueError,json.JSONDecodeError):pass
   else:raise ValueError('malformed JSON accepted:'+raw)
  p.write_text('{"x":[1,2.5,true]}');need(read(p)=={'x':[1,2.5,True]},'valid JSON rejected')
 for text,expected in [("'A' depends on axioms: [sorryAx]",['A']),("'A' depends on axioms: [propext]",['B']),("",['A'])]:
  try:audit(text,expected)
  except ValueError:pass
  else:raise ValueError('invalid axiom receipt accepted')
 need(audit("'A' depends on axioms: [propext, Classical.choice, Quot.sound]",['A'])[0]['theorem']=='A','valid audit rejected')

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True)
 p.add_argument('--check',action='store_true');p.add_argument('--self-test',action='store_true');a=p.parse_args();out=a.out.resolve()
 if a.self_test:self_test();print('PASS_STRICT_JSON_AND_AXIOM_NEGATIVE_TESTS');return
 need(not out.exists(),'fresh output required');manifest=read(B/'OCTIC_MANIFEST.json')
 need(sha(OLD/'integration/SOURCE_CLOSURE.json')==manifest['original_manifest_sha256'],'original source manifest pin')
 original=read(OLD/'integration/SOURCE_CLOSURE.json')['modules'];need(len(original)==111,'complete111-source scope')
 need(len(set(x['module']for x in original))==111,'duplicate original module')
 original_rows=[]
 for r in original:
  f=OLD/'integration'/r['frozen'];need(sha(f)==r['sha256'],'old frozen source identity:'+r['module'])
  original_rows.append({'module':r['module'],'path':f,'sha256':r['sha256'],'audits':manifest['original_final_audits']if r['module']=='NetworkConsumers'else None})
 new_rows=[]
 for r in manifest['new_modules']:
  f=B/r['path'];need(sha(f)==r['sha256'],'new source identity:'+r['module'])
  new_rows.append({**r,'path':f})
 ref=read(OLD/'scripts/GENERIC_CONTEXT.json');ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',OLD/'scripts/GENERIC_CONTEXT.json')))
 need(ctx['compiler_sha256']==COMPILER_SHA==sha(ctx['compiler']),'compiler pin')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in ref['generic_dependencies']],'generic source pins')
 for d in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic revision:'+d['name'])
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'modified generic tracked sources:'+d['name'])
 need(ctx['generic_libraries']==[d['library']for d in ctx['generic_dependencies']if d['library_present']],'generic-only library route')
 if a.check:print('PASS_COMMON_SOURCE_PREFLIGHT_ONLY');return
 out.mkdir(parents=True);src=out/'source';obj=out/'objects';logs=out/'logs'
 src.mkdir();obj.mkdir();logs.mkdir();(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
 (out/'OCTIC_MANIFEST.executed.json').write_bytes((B/'OCTIC_MANIFEST.json').read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(obj),*ctx['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None)
 start=time.monotonic();rows=[];audits=[]
 for r in original_rows+new_rows:
  mod=r['module'];rel=mod.replace('.','/');target=src/(rel+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(r['path'].read_bytes())
  o=obj/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
  cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(o),str(target)]
  before=time.monotonic();run=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,
    preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
  (logs/(mod+'.stdout')).write_text(run.stdout);(logs/(mod+'.stderr')).write_text(run.stderr)
  rr={'module':mod,'source_sha256':sha(target),'returncode':run.returncode,'seconds':time.monotonic()-before,'command':['/usr/bin/time','-v',*cmd],'memory_cap_bytes':80*1024**3,'Lean_threads':8,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr).group(1))}
  if run.returncode==0:rr['object_sha256']=sha(o)
  rows.append(rr);save(out/'BUILD.json',{'status':'RUNNING'if run.returncode==0 else'FAIL','compiler_sha256':COMPILER_SHA,'modules':rows})
  need(run.returncode==0,'source compilation failed:'+mod)
  need(sha(r['path'])==r['sha256']==sha(target),'source changed:'+mod)
  if r['audits']is not None:audits+=audit(run.stdout,r['audits'])
  print(mod,run.returncode,round(rr['seconds'],2),flush=True)
 need(len(rows)==117,'incomplete source closure');need(sha(B/'OCTIC_MANIFEST.json')==sha(out/'OCTIC_MANIFEST.executed.json'),'manifest changed')
 for row in rows:
  rel=row['module'].replace('.','/');need(sha(src/(rel+'.lean'))==row['source_sha256']and sha(obj/(rel+'.olean'))==row['object_sha256'],'source/object binding changed')
 save(out/'BUILD.json',{'status':'PASS','compiler_sha256':COMPILER_SHA,'modules':rows})
 result={'schema':'RH_LIMIT_COLD117_OCTIC_V1','status':'PASS_COMPLETE_SAME_SOURCE111_PLUS_FOUR_CLOSED_OCTIC_CONTRACTS','seconds':time.monotonic()-start,'compiler_sha256':COMPILER_SHA,'controller_sha256':sha(__file__),'manifest_sha256':sha(B/'OCTIC_MANIFEST.json'),'python_optimization':sys.flags.optimize,'original_modules':111,'new_modules':6,'no_prebuilt_application_objects':True,'axiom_audits':audits,'BUILD_sha256':sha(out/'BUILD.json'),'peak_child_RSS_KiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'final_owned_bytes':sum(f.stat().st_size for f in out.rglob('*')if f.is_file()),'peak_disk':'not sampled','OOM':'all117 accepted jobs returned0; kernel OOM counter not independently sampled','full_EF_or_zero_estimate_closed':False,'four_octic_contracts_closed':True,'remaining_contracts':['EvenKernel.ExplicitFormula','EvenKernel.ZeroEstimate'],'source_first_PV':False}
 save(out/'RESULT.json',result);print(result['status'],flush=True)
if __name__=='__main__':main()
