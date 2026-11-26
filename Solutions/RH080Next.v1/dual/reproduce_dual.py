#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Source-cold reproduction of the actual-C, unrestricted-CMS theorem closure.
Only pinned generic packages are reused; every application module is rebuilt.
No native_decide, sorry, unverified numerical premise, or author Comparator receipt.
"""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,tempfile,time
from pathlib import Path

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):
 need(p.is_file()and not p.is_symlink(),'Missing or aliased source: '+str(p))
 return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'Duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_bytes(),object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in()).throw(ValueError(s)))
def publish(p,d):
 need(not os.path.lexists(p),'Fresh receipt required')
 fd,n=tempfile.mkstemp(prefix='.receipt-',dir=p.parent)
 try:
  with os.fdopen(fd,'w')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(n,p)
 finally:Path(n).unlink()
def context(path,R):
 c=load(path);pin=load(R/'Solutions/RH080Study.v1/estimates/DEPENDENCY_PINS.json')
 compiler=Path(c['compiler']).resolve(strict=True)
 need(sha(compiler)==c['compiler_sha256']==pin['compiler_sha256'],'Compiler hash mismatch')
 need(subprocess.check_output([str(compiler),'--version'],text=True).strip()==c['compiler_version']==pin['compiler_version'],'Compiler version mismatch')
 paths=c['generic_lean_path'].split(':');deps=pin['generic_dependencies']
 need(len(paths)==len(set(paths))==len(deps)==8,'Eight pinned generic libraries required')
 for n,dep in zip(paths,deps):
  lib=Path(n);need(lib.is_absolute()and lib.is_dir()and lib.parts[-4:]==('.lake','build','lib','lean'),'Bad generic library layout')
  pkg=lib.parents[3];need(pkg.name==dep['name'],'Generic package identity/order mismatch')
  need(subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD'],text=True).strip()==dep['revision'],'Generic package revision mismatch')
  need(not subprocess.check_output(['git','-C',str(pkg),'status','--porcelain','--untracked-files=no'],text=True),'Dirty generic sources')
 return c

def main():
 a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--repository',type=Path,required=True);a.add_argument('--context',type=Path,required=True);a.add_argument('--run',type=Path,required=True);a.add_argument('--workers',type=int,default=4);a.add_argument('--check-only',action='store_true');o=a.parse_args()
 R=o.repository.resolve(strict=True);need(not os.path.lexists(o.run),'Fresh run required');need(1<=o.workers<=16,'Workers must be1..16');c=context(o.context,R)
 old=R/'Solutions/RH080Study.v1';new=R/'Solutions/RH080Next.v1/dual';roots=[new,old/'functional',old/'pv/lean',old/'sine',R/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source'];generic=('Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets');modules={};visiting=set();order=[]
 def visit(n):
  if n in modules:return
  if any(n==g or n.startswith(g+'.')for g in generic):return
  need(n not in visiting,'Import cycle '+n);visiting.add(n)
  matches=[(r,r.joinpath(*n.split('.')).with_suffix('.lean'))for r in roots];matches=[(r,p)for r,p in matches if p.is_file()]
  need(matches,'Missing application dependency: '+n);need(len(matches)==1,'Ambiguous application module: '+n)
  base,p=matches[0];need(p.resolve().is_relative_to(R),'Source escapes repository')
  imports=[v for line in p.read_text().splitlines()if line.startswith('import ')for v in line[7:].split('--',1)[0].split()]
  for v in imports:visit(v)
  visiting.remove(n);modules[n]={'source':str(p.relative_to(R)),'source_root':str(base.relative_to(R)),'sha256':sha(p),'imports':imports};order.append(n)
 visit('DualCampaignAudit')
 need('GoldbachDirect.Correspondence.Specification'in modules and 'LeanCert.Core.Taylor'in modules,'Incomplete syntax/analytic closure')
 o.run.mkdir(parents=True);plan={'status':'PREFLIGHT_ONLY'if o.check_only else'FROZEN_FULL_SOURCE_COLD_PLAN','controller_sha256':sha(Path(__file__)),'context_sha256':sha(o.context),'compiler_sha256':c['compiler_sha256'],'modules':modules,'order':order,'workers':o.workers,'lean_threads':1,'generic_libraries':c['generic_lean_path'].split(':'),'command':list(os.sys.argv)};publish(o.run/'PLAN.json',plan)
 if o.check_only:print('PREFLIGHT_ONLY',len(modules));return
 bank=o.run/'objects';bank.mkdir();env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);done=set();active={};rows=[];start=time.monotonic()
 def build(n):
  row=modules[n];p=R/row['source'];dest=bank.joinpath(*n.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);tag=n.replace('.','_');stdout=o.run/(tag+'.stdout');stderr=o.run/(tag+'.stderr');tm=o.run/(tag+'.time');t=time.monotonic();cmd=[c['compiler'],'-j1','-R',str(R/row['source_root']),'-o',str(dest),str(p)]
  with stdout.open('x')as f,stderr.open('x')as g:v=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],env=env,stdout=f,stderr=g)
  need(sha(p)==row['sha256'],'Source changed during compile '+n)
  rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm.read_text())
  result={'module':n,'returncode':v.returncode,'seconds':time.monotonic()-t,'maximum_RSS_KiB':int(rss.group(1))if rss else None,'source_sha256':row['sha256'],'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'command':cmd}
  if v.returncode==0:result['object_sha256']=sha(dest)
  publish(o.run/(tag+'.COMPILED.json'),result);return result
 with concurrent.futures.ThreadPoolExecutor(max_workers=o.workers)as ex:
  while len(done)<len(modules):
   for n in order:
    if len(active)>=o.workers:break
    if n not in done and n not in active.values()and all(v not in modules or v in done for v in modules[n]['imports']):active[ex.submit(build,n)]=n
   need(active,'Dependency deadlock')
   finished,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in finished:
    n=active.pop(f);r=f.result();rows.append(r);need(r['returncode']==0,'Compilation failed '+n);done.add(n);print('compiled',len(done),'/',len(modules),n,flush=True)
 audit=(o.run/'DualCampaignAudit.stdout').read_text();facts=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
 expected=['abel_fourier_inversion','abel_real_inversion_zero','weak_duality_cms','weak_duality_even_cms','functional_lower_bound_even_cms','source_first_full_cms_lower_bound','source_first_full_cms_excludes_four_fifths','source_first_full_cms_result','nonnegative_coupled_cms_bound','sine_ratio_order','cosine_square_tangent']
 need([n for n,_ in facts]==['RH080Next.Dual.'+n for n in expected],'Missing, duplicated or changed audited theorem')
 for n,axioms in facts:need(set(x.strip()for x in axioms.split(',')if x.strip())<= {'propext','Classical.choice','Quot.sound'},'Unapproved axiom in '+n)
 for n,row in modules.items():need(sha(R/row['source'])==row['sha256'],'Final source changed '+n)
 need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed during execution')
 disk=sum(p.stat().st_size for p in o.run.rglob('*')if p.is_file())
 result={'status':'PASS_FRESH_SOURCE_FIRST_FULL_CMS_CLOSURE_STANDARD_AXIOMS_ONLY','modules':len(modules),'theorems':len(facts),'seconds':time.monotonic()-start,'disk_bytes':disk,'maximum_individual_Lean_RSS_KiB':max(r['maximum_RSS_KiB']or 0 for r in rows),'axioms':{n:[x.strip()for x in v.split(',')]for n,v in facts},'plan_sha256':sha(o.run/'PLAN.json'),'controller_sha256':plan['controller_sha256'],'official_Comparator_acceptance':False,'numerical_cap':'123/100 from existing actual-source-C execution; no new compiled-platform correctness axiom','stronger_external_Arb_cap_Lean_closed':False};publish(o.run/'RESULT.json',result);print(result['status'])
if __name__=='__main__':main()
