#!/usr/bin/env python3
"""Normal current-core CLI, serialized AFTER fresh bootstrap and proof gates.
Run only under the owned generic resource guard; does not claim Comparator/PV.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,subprocess,sys,tempfile,time

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(8*2**20),b''):h.update(b)
 return h.hexdigest()
def publish(p,j):
 need(not os.path.lexists(p),'Fresh phase receipt required');fd,tmp=tempfile.mkstemp(dir=p.parent)
 try:
  with os.fdopen(fd,'w')as f:json.dump(j,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(tmp,p)
 finally:
  if os.path.lexists(tmp):os.unlink(tmp)
def output(args,cwd):
 r=subprocess.run(args,cwd=cwd,capture_output=True,text=True,env=dict(os.environ,GIT_OPTIONAL_LOCKS='0'));need(r.returncode==0,'Read-only identity command failed');return r.stdout

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--python',type=Path,required=True);a=ap.parse_args()
 R=a.repository.resolve(strict=True);context=a.context.resolve(strict=True);run=a.run.resolve();need(not os.path.lexists(run),'Fresh normal CLI workspace required');run.mkdir(parents=True)
 S=R/'Solutions/RH080Next.v1';spec=importlib.util.spec_from_file_location('bootstrap',S/'reproduction/bootstrap_context.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
 c,roots=helper.validate_context(helper.read_json(context));compiler=Path(c['compiler']);lake=compiler.parent/'lake';need(lake.is_file(),'Pinned Lake binary missing')
 need(output([str(a.python),'-c','import importlib.metadata;print(importlib.metadata.version("PyYAML"))'],R).strip()=='6.0.3','Exact normal CLI PyYAML6.0.3 required')
 manifest=helper.read_json(R/'lake-manifest.json');expected={row['name']:row['rev']for row in manifest['packages']};need(len(expected)==9,'Pinned core dependency count differs')
 for row in c['generic_dependencies']:need(expected[row['name']]==row['revision'],'Fresh generic and normal core pin differ')
 packages=[]
 for name,revision in expected.items():
  p=R/'.lake/packages'/name;need(p.is_dir()and not p.is_symlink()and p.resolve().is_relative_to(R/'.lake'),'Owned independent normal cache required')
  need(output(['git','-C',str(p),'rev-parse','HEAD'],R).strip()==revision,'Normal generic revision differs')
  need(not output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],R).strip(),'Normal generic tracked source is dirty')
  gitdir=Path(output(['git','-C',str(p),'rev-parse','--absolute-git-dir'],R).strip());need(gitdir.is_relative_to(R/'.lake'),'Generic Git directory outside owned cache')
  packages.append(dict(name=name,revision=revision,path=str(p),gitdir=str(gitdir)))
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',GIT_OPTIONAL_LOCKS='0',ELAN_TOOLCHAIN='leanprover/lean4:v4.34.0-rc2',PATH=str(compiler.parent)+os.pathsep+os.environ['PATH'])
 for n in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_HOME','LAKE_PACKAGES_DIR']:env.pop(n,None)
 for n,leaf in [('MATHLIB_CACHE_DIR','mathlib'),('LAKE_CACHE_DIR','lake'),('XDG_CACHE_HOME','xdg'),('TMPDIR','tmp'),('TMP','tmp'),('TEMP','tmp')]:
  p=run/'cache'/leaf;p.mkdir(parents=True,exist_ok=True);env[n]=str(p)
 sources={}
 for folder,dirs,names in os.walk(R,followlinks=False):
  dirs[:]=[n for n in dirs if n not in ['.git','.lake','__pycache__']and not(Path(folder)/n).is_symlink()]
  for n in names:
   p=Path(folder)/n
   if p.is_symlink()or p.name=='fingerprints.json':continue
   sources[str(p.relative_to(R))]=sha(p)
 source_manifest=run/'PROTECTED_SOURCE_INVENTORY.json';publish(source_manifest,dict(files=sources,HEAD=output(['git','rev-parse','HEAD'],R).strip()))
 baseline=helper.read_json(S/'explicit/CANONICAL_W4_BASELINE.json')
 need(len(baseline['files'])==26,'Exact original26-file node baseline missing')
 for row in baseline['files']:need(sha(R/row['file'])==row['sha256'],'Original26-file node baseline changed before normal CLI')
 commands=[[str(lake),'build','IEANTN','ieantn_hash'],[str(a.python),str(R/'scripts/ieantn.py'),'fingerprint']]
 checks=[['fingerprint','--check'],['check-graph'],['check-closure'],['check-pins'],['gen-challenges','--check'],['check-receipts'],['check']]
 for flags in [[],['-O'],['-OO']]:commands += [[str(a.python)]+flags+[str(R/'scripts/ieantn.py')]+args for args in checks]
 plan=dict(status='NORMAL_CLI_EXECUTION_REQUESTED_NOT_PROOF_ACCEPTANCE',commands=commands,context_sha256=sha(context),compiler_sha256=sha(compiler),lake_sha256=sha(lake),source_inventory_sha256=sha(source_manifest),nine_owned_package_pins=packages,cache_environment={n:env[n]for n in ['MATHLIB_CACHE_DIR','LAKE_CACHE_DIR','XDG_CACHE_HOME','TMPDIR','TMP','TEMP']},only_intended_source_writes='node fingerprints.json and removal of legacy root fingerprints.json',protected_original_generic_roots_not_used_as_mutable_cache=True,source_sha256=sha(Path(__file__)))
 publish(run/'PLAN.json',plan);start=time.monotonic();records=[]
 try:
  for i,cmd in enumerate(commands):
   tick=time.monotonic()
   timed=['/usr/bin/time','-v','-o',str(run/f'{i}.time')]+cmd
   with(run/f'{i}.stdout').open('xb')as o,(run/f'{i}.stderr').open('xb')as e:r=subprocess.run(timed,cwd=R,env=env,stdout=o,stderr=e)
   timefile=run/f'{i}.time';need(timefile.is_file(),'Actual GNU-time receipt missing')
   rss=re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',timefile.read_text())
   need(len(rss)==1,'Exact one GNU maximum-RSS field required')
   row=dict(command=cmd,actual_timed_command=timed,returncode=r.returncode,seconds=time.monotonic()-tick,stdout_sha256=sha(run/f'{i}.stdout'),stderr_sha256=sha(run/f'{i}.stderr'),GNU_time_sha256=sha(timefile),GNU_max_RSS_KiB=int(rss[0]),actual_returncode_not_GNU_text_is_authoritative=True);publish(run/f'{i}.RECEIPT.json',row);records.append(row)
   if i<2:need(r.returncode==0,'Normal build/fingerprint generation failed; dependent checks not run')
   if i==0:
    diagnostics=(run/f'{i}.stdout').read_text(errors='replace')+(run/f'{i}.stderr').read_text(errors='replace')
    need('PANIC'not in diagnostics and 'uncaught exception'not in diagnostics.lower(),'Compiler diagnostics invalidate the normal build despite exit0')
    need((R/'.lake/build/bin/ieantn_hash').is_file()and(R/'.lake/build/lib/lean/IEANTN.olean').is_file(),'Normal built core or hash binary absent')
  for rel,digest in sources.items():need((R/rel).is_file()and sha(R/rel)==digest,'Protected source changed during normal CLI: '+rel)
  for row in baseline['files']:need(sha(R/row['file'])==row['sha256'],'Original26-file node baseline changed during normal CLI')
  failed=[row for row in records if row['returncode']!=0]
  need(not failed,'One or more actual strict normal/O/OO CLI checks failed; all completed checks retained')
  fingerprints={str(p.relative_to(R)):sha(p)for p in (R/'IEANTN').rglob('fingerprints.json')}
  need(fingerprints,'No current canonical fingerprints generated')
  publish(run/'RESULT.json',dict(status='PASS_NORMAL_UPDATED_CORE_LAKE_HASHER_AND_ALL_MODE_STRICT_CLI_NOT_COMPARATOR',records=records,seconds=time.monotonic()-start,fingerprints=fingerprints,protected_source_files_rechecked=len(sources),source_inventory_sha256=sha(source_manifest),source_sha256=sha(Path(__file__)),built_ieantn_hash_sha256=sha(R/'.lake/build/bin/ieantn_hash'),built_IEANTN_olean_sha256=sha(R/'.lake/build/lib/lean/IEANTN.olean'),Tools_Hash_source_sha256=sha(R/'Tools/Hash.lean'),maximum_command_GNU_RSS_KiB=max(row['GNU_max_RSS_KiB']for row in records),GNU_time_binary_sha256=sha(Path('/usr/bin/time')),official_Comparator_run=False,source_first_PV_claimed=False))
 except BaseException as e:
  publish(run/'INCOMPLETE.json',dict(status='INCOMPLETE_NORMAL_CORE_CLI',error=type(e).__name__+': '+str(e),records=records,seconds=time.monotonic()-start));raise
 print('PASS normal core CLI; no official Comparator claim')
if __name__=='__main__':main()
