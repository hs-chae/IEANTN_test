#!/usr/bin/env python3
"""Run the actual repository fingerprint command in a fresh isolated core copy.
Never build in the development symlink overlay, and never copy old fingerprints
back. A later call after the last node freeze is the authoritative capture.
"""
from pathlib import Path
import argparse,hashlib,json,os,resource,shutil,subprocess,time
R=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--copy-new',action='store_true');a=p.parse_args();out=a.out.resolve()
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
need(not out.exists(),'fresh isolated output required');out.mkdir();core=out/'core-source';core.mkdir()
for name in ['IEANTN','Tools','scripts']:shutil.copytree(R/name,core/name,ignore=shutil.ignore_patterns('__pycache__'))
for name in ['IEANTN.lean','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(R/name,core/name)
(core/'.lake').mkdir();(core/'.lake/packages').symlink_to((R/'.lake/packages').resolve(),target_is_directory=True)
old=json.loads((HERE/'PRE_EDIT_BASELINE.json').read_text())['protected_old_IEANTN_files'];before={str(f.relative_to(core)):sha(f)for f in(core/'IEANTN/Nodes').glob('*/*/fingerprints.json')};env=os.environ.copy();env['LEAN_NUM_THREADS']='4';env['PYTHONDONTWRITEBYTECODE']='1';env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
cmd=['/data/ivy-rh-octic-20261123/tooling-venv/bin/python','scripts/ieantn.py','fingerprint'];t=time.monotonic()
(out/'COMMAND.json').write_text(json.dumps({'command':cmd,'controller_sha256':sha(Path(__file__)),'PID':os.getpid(),'status':'RUNNING_NOT_ACCEPTED'},indent=2)+'\n')
with (out/'stdout').open('w')as so,(out/'stderr').open('w')as se:
 cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=core,env=env,text=True,stdout=so,stderr=se,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(128<<30,128<<30)))
need(cp.returncode==0,'actual repo fingerprint command failed; retained logs')
changes=[];copied=[]
for f in sorted((core/'IEANTN/Nodes').glob('*/*/fingerprints.json')):
 rel=str(f.relative_to(core))
 if rel in old:
  if sha(f)!=old[rel]:changes.append({'path':rel,'old_sha256':old[rel],'recomputed_sha256':sha(f)})
 elif a.copy_new:
  target=R/rel;need(target.parent.exists(),'new fingerprint target absent');target.write_bytes(f.read_bytes());copied.append({'path':rel,'sha256':sha(f)})
for rel,h in old.items():need(sha(R/rel)==h,'protected old source changed')
result={'status':'PASS_ACTUAL_ISOLATED_CORE_FINGERPRINT_COMMAND','command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,'core_source_root':str(core),'old_fingerprint_churn_in_isolated_copy':changes,'new_fingerprints_copied':copied,'repo_old_files_unchanged':len(old),'repository_development_overlay_used':False,'stdout_sha256':sha(out/'stdout'),'stderr_sha256':sha(out/'stderr')};(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in['status','seconds','old_fingerprint_churn_in_isolated_copy','new_fingerprints_copied']}))
