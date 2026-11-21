#!/usr/bin/env python3
"""Prepare the pinned generic environment, or validate an existing context.

Application proof objects are never an input. A network bootstrap downloads
Lean/Mathlib dependencies; ordinary proof replays can then run offline.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(cmd,cwd):
 p=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True)
 if p.returncode:raise RuntimeError('command failed '+repr(cmd)+'\n'+p.stderr[-4000:])
 return p.stdout.strip()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--existing-context',type=Path);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh output required');O.mkdir(parents=True)
reference=json.loads((S/'MertensPositive/BUILD_CONTEXT.json').read_text());started=time.monotonic()
if a.existing_context:
 c=json.loads(a.existing_context.read_text());need(c['compiler_sha256']==reference['compiler_sha256'],'compiler contract');need(c['pinned_mathlib_revision']==reference['pinned_mathlib_revision'],'mathlib identity')
else:
 need(shutil.which('elan')is not None,'Install elan first: https://github.com/leanprover/elan#installation; then rerun this command')
 project=O/'generic';project.mkdir()
 for n in ['lakefile.toml','lean-toolchain']:shutil.copyfile(S/'MertensPositive'/n,project/n)
 run(['elan','toolchain','install','leanprover/lean4:v4.34.0-rc2'],project)
 run(['lake','update'],project)
 run(['lake','exe','cache','get'],project)
 compiler=Path(run(['elan','which','lean'],project))
 c=dict(reference);c['compiler']=str(compiler);c['generic_libraries']=[];c['generic_dependencies']=[]
 for old in reference['generic_dependencies']:
  dep=project/'.lake/packages'/old['name'];row=dict(old);row['path']=str(dep);row['library']=str(dep/'.lake/build/lib/lean');row['library_present']=Path(row['library']).is_dir();c['generic_dependencies'].append(row)
  if row['library_present']:c['generic_libraries'].append(row['library'])
need(sha(c['compiler'])==reference['compiler_sha256'],'exact Linux compiler binary required')
expected={d['name']:d['revision']for d in reference['generic_dependencies']}
need({d['name']:d['revision']for d in c['generic_dependencies']}==expected,'exact complete dependency revisions')
for dep in c['generic_dependencies']:
 directory=Path(dep['path']);need(run(['git','rev-parse','HEAD'],directory)==dep['revision'],'dependency commit '+dep['name']);need(not run(['git','status','--porcelain','--untracked-files=no'],directory),'tracked dependency sources changed '+dep['name'])
 if dep.get('library_present'):need(Path(dep['library']).is_dir(),'generic objects missing '+dep['name'])
c['source_root']=str(S/'MertensPositive');c['new_application_object_root']=str(O/'unused-new-application');c['reused_application_proof_objects']=False
(O/'GENERIC_CONTEXT.json').write_text(json.dumps(c,indent=2)+'\n')
receipt={'status':'PASS_PINNED_GENERIC_ENVIRONMENT','compiler_sha256':sha(c['compiler']),'generic_dependencies':expected,'source_context_sha256':sha(a.existing_context)if a.existing_context else None,'bootstrap_sha256':sha(__file__),'elapsed_seconds':time.monotonic()-started,'network_bootstrap_executed':a.existing_context is None,'no_application_objects_used':True};(O/'BOOTSTRAP_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(O/'GENERIC_CONTEXT.json')
