#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,shutil,sys,time
W=Path('/ryu/hyunsik/playground/independence/codex/ivy');R=W/'ieantn-rh-propagation-20261120';D=Path('/data/ivy-rh-propagation-20261120');N=R/'network'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(8*1024**2),b''):h.update(b)
 return h.hexdigest()
def write(p,d):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n')
def tree(root,out):
 rows=[]
 for base,dirs,files in os.walk(root,followlinks=False):
  for name in sorted(dirs+files):
   p=Path(base,name);rel=p.relative_to(root).as_posix()
   if p.is_symlink():
    if not p.resolve().is_relative_to(root.resolve()):raise RuntimeError('external symlink '+str(p))
    rows.append({'path':rel,'symlink':os.readlink(p)})
   elif p.is_file():rows.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)})
   elif not p.is_dir():raise RuntimeError('nonregular exposureentry')
 rows.sort(key=lambda r:r['path']);write(out,{'root':str(root),'files':rows});print(json.dumps({'tree':str(root),'files':len(rows),'bytes':sum(r.get('bytes',0)for r in rows),'manifest':str(out)}),flush=True)
 return {'path':str(out),'sha256':sha(out)}
def main():
 generic=json.loads((R/'protocol/GENERIC_RUNTIME.json').read_text())
 # Earlier generic generation has deterministic hashes but must globally sort to match strict runtime inventory.
 common=[]
 for row in generic['mounts']:
  row=dict(row);p=Path(row['manifest']['path']);d=json.loads(p.read_text());d['files'].sort(key=lambda r:r['path']);write(p,d);row['manifest']={'path':str(p),'sha256':sha(p)}
  row['target']=row['target'].replace('/generic-source/','/generic/source/').replace('/generic-lib/','/generic/lib/');common.append(row)
 lean=[p.replace('/generic-lib/','/generic/lib/')for p in generic['lean_path']]
 fulltree=tree(N,R/'protocol/trees/FULL_IEANTN.json')
 cache=Path('/data/ivy-ramanujan-source-pv-20261119/lean');cachetree=tree(cache,R/'protocol/trees/APPLICATION_CACHE.json')
 for arm in ['NL_RH','IEANTN_RH']:
  packet=R/'protocol/packets'/arm
  literature=D/'literature'/arm;lit=tree(literature,R/'protocol/trees'/('LITERATURE_'+arm+'.json'))
  mounts=common+[{'source':str(literature),'target':'/corpus/literature','role':'literature','appendable_broker_only':True,'manifest':lit}]
  paths=lean+['/work']
  if arm=='IEANTN_RH':
   mounts.extend([{'source':str(N),'target':'/ieantn','role':'application','manifest':fulltree},{'source':str(cache),'target':'/application-cache','role':'application','manifest':cachetree}]);paths.extend(['/application-cache','/ieantn'])
  runtime={'schema':'RH_PROPAGATION_RUNTIME_V1','arm':arm,'mounts':mounts,'lean_path':paths,'required_imports':['Mathlib.NumberTheory.LSeries.RiemannZeta'],'forbidden_imports':['HiddenStudyAnswer']+(['IEANTN','RamanujanPV.FinalAnalytic']if arm=='NL_RH'else[]),'forbidden_paths':[str(R/'evaluator-private/SECRET_CANARY.txt'),str(D/'literature'/('IEANTN_RH'if arm=='NL_RH'else'NL_RH')/'INITIAL_SOURCE_LEDGER.json')],'external_network':False,'host_tools':False,'source_policy':'Identical initial primary sources and independent open legitimate-source broker. Only full arm receives existing project sources/application cache. Current evaluator/otherarm/memory never mounted.'}
  # /work is private writable and injected by executor, rather than a host mount.
  runtime['lean_path']=[p for p in paths if p!='/work']
  write(R/'protocol'/('runtime-'+arm+'.json'),runtime)
  visible={'arm':arm,'read_only_mounts':[{'target':row['target'],'role':row['role']}for row in mounts],'lean_path':['/work']+runtime['lean_path'],'source_access':'/task/request_source.py; results under /corpus/literature/admissions, perrequest receipts'}
  write(packet/'RUNTIME_PATHS.json',visible)
  (packet/'TOOLS.md').write_text('# Generic tools\n\nUse /opt/lean/bin/lean for pinned Lean4.34rc2, /usr/bin/gcc or /usr/bin/g++ for ordinary C/C++, /usr/bin/python3.10 for Python with mpmath1.3.0 and sympy1.12. Shell /bin/bash must be non-login. The LEAN_PATH environment lists your assigned pinned library roots; add /work or your own object root when compiling local modules. No shared host cache or HOME is available.\n\nCompile example: /opt/lean/bin/lean -o /work/Example.olean /work/Example.lean . You may inspect generic source under /generic/source/PACKAGE. The toolchain includes Lake, but network downloads inside worker are blocked; dependency sources/objects are already provided identically. Generic caches are read-only. Source requests do not block research; save otherwork and inspect admissions after a technical snapshot.\n')
  tree(packet,R/'protocol'/('packet-manifest-'+arm+'.json'))
 (R/'evaluator-private/SECRET_CANARY.txt').write_text('EVALUATOR_ONLY_RH_EXPERIMENT_CANARY\n')
 write(R/'protocol/RUNTIME_PREPARATION.json',{'completed_utc':__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),'source_aggregate_sha256':fulltree['sha256'],'application_cache_manifest':cachetree,'generic_identical':True,'scored_workers_launched':False})
if __name__=='__main__':main()
