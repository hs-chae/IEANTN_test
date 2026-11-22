#!/usr/bin/env python3
"""Clean source replay plus all five canonical public solution adapters."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time,re,os
HERE=Path(__file__).resolve().parent;N=HERE.parents[2]
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh output required');out.mkdir(parents=True);start=time.monotonic();own=sha(__file__)
 need((N/'IEANTN/Nodes').is_dir(),'network source root missing')
 for row in read(HERE/'PUBLIC_SOLUTIONS.json')['files']:need(sha(N/row['path'])==row['sha256'],'canonical source preflight failed')
 if a.base_run:base=a.base_run.resolve()
 else:
  base=out/'base';subprocess.run([sys.executable,str(HERE/'reproduce.py'),'--out',str(base)],check=True)
 receipt=read(base/'RESULT.json');build=read(base/'BUILD.json');manifest=read(HERE/'SOURCE_CLOSURE.json');need(receipt['status']=='PASS_COMPLETE_SOURCE_ONLY_INTEGRATED_PROOFS'and build['status']=='PASS','base source replay incomplete');need(receipt['source_manifest_sha256']==sha(HERE/'SOURCE_CLOSURE.json'),'different source closure');need(len(build['modules'])==len(manifest['modules']),'partial source closure');need(not build['extra_libraries'],'base uses declared app objects; source-only basis required')
 for r,m in zip(build['modules'],manifest['modules']):
  need(r['module']==m['module']and r['returncode']==0 and r['source_sha256']==m['sha256'],'base source mismatch');obj=base/'objects'/(r['module'].replace('.','/')+'.olean');need(obj.is_file(),'base object missing')
  need(isinstance(r.get('object_sha256'),str)and len(r['object_sha256'])==64,'base has no recorded object identity; regenerate with current helper')
  need(sha(obj)==r['object_sha256'],'base object altered')
 selected=read(HERE/'PUBLIC_SOLUTIONS.json');src=out/'source';src.mkdir();modules=[]
 for row in selected['files']:
  original=N/row['path'];need(sha(original)==row['sha256'],'canonical public proof changed');(src/(row['module']+'.lean')).write_bytes(original.read_bytes());modules.append(row['module'])
 command=[sys.executable,str(HERE.parent/'scripts/build_modules.py'),'--source',str(src),'--out',str(out/'public'),'--extra-library',str(base/'objects')]
 for m in modules:command+=['--module',m]
 subprocess.run(command,check=True);audits=[]
 for row in selected['files']:
  raw=(out/'public/logs'/(row['module']+'.stdout')).read_text()
  for name in row['theorems']:
   hits=re.findall("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",raw);need(len(hits)==1,'public axiom audit missing:'+name);found={v.strip()for v in hits[0].split(',')};need(found=={'propext','Classical.choice','Quot.sound'},'public theorem unexpected axiom:'+name);audits.append({'theorem':name,'axioms':sorted(found)})
 need(sha(__file__)==own,'reproducer changed during run');result={'status':'PASS_COMPLETE_PUBLIC_SOLUTION_SOURCE_REPLAY','seconds':time.monotonic()-start,'base':str(base),'base_result_sha256':sha(base/'RESULT.json'),'source_modules':len(manifest['modules'])+len(modules),'public_theorems':audits,'public_source_manifest_sha256':sha(HERE/'PUBLIC_SOLUTIONS.json'),'validator_sha256':own,'source_first_PV':'This replay audits the kernel analytic edge closure only; the separate C-log and coefficient source-first replays have their own receipts and explicit mathematical premises.'};temp=out/'RESULT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');os.replace(temp,out/'RESULT.json');print(json.dumps({'status':result['status'],'modules':result['source_modules'],'seconds':result['seconds']}))
if __name__=='__main__':main()
