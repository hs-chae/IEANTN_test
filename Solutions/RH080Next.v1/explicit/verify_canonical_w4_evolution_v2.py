#!/usr/bin/env python3
"""Exact canonical claims/dependencies and disjoint typed-entry verifier.
Local proof evidence only; no official Comparator receipt. The production
CLI is fixed to the29-claim W4 scope. Fixture callers use the reusable core
and publish a distinct fixture-only status.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
import yaml
ROOT=Path(__file__).resolve().parents[3]
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
NODES={
 'W4FourierNorm.v1':['l1_bound'],
 'RHGlobalAffineIntervals.v1':['global_0851062','branch_0777','branch_074','branch_075','branch_08','branch_0851062','piecewise_strict'],
 'RHAnalyticFlatPopulation.v1':['family_curve','family_infimum','flat64_curve','forty_population','adaptive_limit','adaptive_population'],
 'RHWeightedPopulation.v2':['sparse_curve','flat_curve','frontier_curve','frontier_count','one_population','ten_population','below_octic_leading_frontier','w4_curve','w4_infimum_strict','three_frontier_curve','actual_below_both_printed_lines','four_frontier_curve','four_frontier_count','adaptive_frontier_curve','adaptive_frontier_count']}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  while b:=f.read(8*1024*1024):h.update(b)
 return h.hexdigest()
def read_json(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key '+k);d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON '+x)
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=bad)
def atomic(p,value):
 need(not p.exists(),'fresh receipt required');q=p.with_name('.'+p.name+'.tmp')
 with q.open('x')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 try:os.link(q,p)
 finally:q.unlink()
def imports(p):return[n for l in Path(p).read_text().splitlines()if l.startswith('import ')for n in l[7:].split('--',1)[0].split()]
def clean(out,err,allow_sorry=False):
 s=out.read_text()+err.read_text();need(not re.search(r'PANIC|\berror(?:\(|:)',s),'compiler diagnostic rejected')
 if not allow_sorry:need('sorryAx'not in s and 'declaration uses'not in s,'proof admission rejected')
def verify_bank(context,bank,expected_root,marker=None,axiom_prefix=None,axiom_count=0):
 ctx=read_json(context);need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler changed');bank=bank.resolve(strict=True);plan=read_json(bank/'PLAN.json');result=read_json(bank/'RESULT.json')
 need(plan['context_sha256']==sha(context),'context differs');need(plan['roots']==[expected_root],'wrong selected final proof/audit root');need(result['status']=='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY','proof batch incomplete')
 rows=plan['source_rows'];need(len({r['module']for r in rows})==len(rows),'collapsed fresh identities');commands={r['module']:r for r in result['commands']};need(len(commands)==len(result['commands'])and set(commands)=={r['module']for r in rows},'missing/duplicate compiler route');inventory={};peak=0
 for r in rows:
  n=r['module'];d=read_json(bank/(n+'.COMPILED.json'));need(d==commands[n]and type(d['exitcode'])is int and d['exitcode']==0,'failed actual compiler '+n);origin=Path(r['origin']);snapshot=Path(r['snapshot']);obj=bank/'objects'/(n.replace('.','/')+'.olean');need(sha(origin)==sha(snapshot)==r['source_sha256'],'fresh source drift '+n);need(sha(obj)==d['object_sha256'],'fresh object drift '+n)
  need(d['command'][-6:]==[ctx['compiler'],'-j2','--root='+str(bank/'source'),'-o',str(obj),str(snapshot)],'actual compiler invocation differs '+n)
  for ext,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('time','time_sha256')]:need(sha(bank/'logs'/(n+'.'+ext))==d[key],'compiler log drift '+n)
  clean(bank/'logs'/(n+'.stdout'),bank/'logs'/(n+'.stderr'));tm=(bank/'logs'/(n+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm);need(len(rss)==1 and 'Command terminated by signal'not in tm,'resource/signal failure '+n);peak=max(peak,int(rss[0]));inventory[n]=origin
 for r in plan['accepted_dependencies']:
  n=r['module'];need(n not in inventory,'duplicate app module '+n);receipt=Path(r['receipt']);need(sha(receipt)==r['receipt_sha256'],'inherited receipt drift '+n);d=read_json(receipt);need(type(d['exitcode'])is int and d['exitcode']==0,'inherited failed compiler '+n);need(sha(r['source_origin'])==sha(r['snapshot'])==r['source_sha256'],'inherited source drift '+n);need(sha(bank/'objects'/(n.replace('.','/')+'.olean'))==r['object_sha256']==d['object_sha256'],'inherited object drift '+n);inventory[n]=Path(r['source_origin'])
 reached=set();active=set()
 def visit(n):
  if n in reached or n.split('.')[0]in GENERIC:return
  need(n in inventory,'missing actual application import '+n);need(n not in active,'import cycle');active.add(n)
  for child in imports(inventory[n]):visit(child)
  active.remove(n);reached.add(n)
 visit(expected_root);need(reached==set(inventory),'recorded import closure differs')
 text=(bank/'logs'/(expected_root+'.stdout')).read_text()
 if marker is not None:need(text.count(marker)==1,'actual compiled theorem/dependency audit marker absent')
 if axiom_prefix is not None:need(text.count(axiom_prefix)==axiom_count,'theorem audit coverage differs')
 return ctx,plan,result,inventory,peak
class UniqueYaml(yaml.SafeLoader):pass
def unique_mapping(loader,node,deep=False):
 loader.flatten_mapping(node);out={}
 for k,v in node.value:
  key=loader.construct_object(k,deep=deep);need(key not in out,'duplicate YAML key '+str(key));out[key]=loader.construct_object(v,deep=deep)
 return out
UniqueYaml.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,unique_mapping)
def node_spec(repo,node,names):
 family,version=node.split('.');p=repo/'IEANTN/Nodes'/family/version/'formalization.yaml';metadata=yaml.load(p.read_text(),Loader=UniqueYaml);conclusions=metadata['conclusions'];need([r['id']for r in conclusions]==names,'exact canonical claim coverage differs '+node)
 result=[]
 for r in conclusions:
  need(r['declaration']==node+'.'+r['id']and r['challenge']==node+'.challenge_'+r['id'],'written declaration identity differs')
  result.append((r['challenge'],[i['node']+'.'+i['conclusion']for i in r.get('imports',[])],r['declaration']))
 return result
PROBE_HEAD='''import __IMPORT__
import Lean
open Lean Elab Command Meta
run_cmd liftTermElabM do
'''
def probe_source(imported,specs):
 lines=[PROBE_HEAD.replace('__IMPORT__',imported)]
 for actual,premises,target in specs:
  lines+=['  do',f'    let info←getConstInfo `{actual}',f'    let mut expected:=mkConst `{target}']
  for p in reversed(premises):lines.append(f'    expected:=mkForall Name.anonymous BinderInfo.default (mkConst `{p}) expected')
  lines.append(f'    unless (←isDefEq info.type expected) do throwError "Exact generated conditional type differs: {actual}"')
 lines.append('  logInfo "CANONICAL_EXACT_ENTRY_TYPES_PASS"');return'\n'.join(lines)+'\n'
def entries(repo,context,ctx,bank,nodes,out,memory_gib=256):
 need(not out.exists(),'fresh entry route directory required');out.mkdir(parents=True);env=dict(os.environ,LEAN_PATH=str(bank/'objects')+':'+ctx['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1');routes=[]
 for node,names in nodes.items():
  family,version=node.split('.');sol=repo/'Solutions'/node;need((sol/'lean-toolchain').read_bytes()==(repo/'lean-toolchain').read_bytes(),'Solution toolchain differs');need(all(not n.endswith('.Challenge')for n in imports(sol/'Solution.lean')),'Solution imports generated Challenge');cmp=read_json(sol/'comparator.json');need(cmp['challenge_module']=='IEANTN.Nodes.'+node+'.Challenge'and cmp['solution_module']=='Solution','Comparator config modules differ');need(cmp['theorem_names']==[node+'.challenge_'+n for n in names],'Comparator theorem coverage differs');need(set(cmp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},'axiom policy differs');specs=node_spec(repo,node,names)
  for kind,origin,module in [('solution',sol/'Solution.lean','Solution'),('challenge',repo/'IEANTN/Nodes'/family/version/'Challenge.lean','IEANTN.Nodes.'+node+'.Challenge')]:
   run=out/(node+'-'+kind);source=run/'source';objects=run/'objects';snapshot=source/(module.replace('.','/')+'.lean');obj=objects/(module.replace('.','/')+'.olean');snapshot.parent.mkdir(parents=True);obj.parent.mkdir(parents=True);snapshot.write_bytes(origin.read_bytes())
   # One complete application import root avoids nested-namespace shadowing.
   for imported in (bank/'objects').rglob('*.olean'):
    target=objects/imported.relative_to(bank/'objects');target.parent.mkdir(parents=True,exist_ok=True);need(not target.exists(),'duplicate inherited route object');need(imported.stat().st_dev==target.parent.stat().st_dev,'typed route requires same-filesystem immutable hardlinks');os.link(imported,target)
   need(not obj.exists(),'entry output would overwrite an inherited object');localenv=dict(env,LEAN_PATH=str(objects)+':'+ctx['generic_lean_path']);commands=[]
   for label,p,output in [('entry',snapshot,obj),('types',source/'ExactEntryTypes.lean',objects/'ExactEntryTypes.olean')]:
    if label=='types':p.write_text(probe_source(module,specs))
    stdout=run/(label+'.stdout');stderr=run/(label+'.stderr');tm=run/(label+'.time');cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as=unlimited','--stack='+str(256*2**20),'--',ctx['compiler'],'-j2','--root='+str(source),'-o',str(output),str(p)]
    with stdout.open('xb')as o,stderr.open('xb')as e:child=subprocess.run(cmd,cwd=source,env=localenv,stdout=o,stderr=e)
    need(child.returncode==0 and output.is_file(),'typed entry route failed '+node+' '+kind+' '+label);clean(stdout,stderr,allow_sorry=(kind=='challenge'and label=='entry'))
    if label=='types':need(stdout.read_text().count('CANONICAL_EXACT_ENTRY_TYPES_PASS')==1,'exact type gate absent')
    commands.append(dict(label=label,command=cmd,exitcode=child.returncode,source_sha256=sha(p),object_sha256=sha(output),stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),time_sha256=sha(tm)))
   routes.append(dict(node=node,kind=kind,module=module,origin=str(origin),source_sha256=sha(origin),commands=commands))
 return routes


AS_POLICY = "EXPLICIT_RLIM_INFINITY_WITH_SEPARATE_PHYSICAL_CGROUP"
PHYSICAL_BYTES = 300 * 2**30

def physical_guard():
 import resource
 rows = Path('/proc/self/cgroup').read_text().splitlines()
 unified = [row[3:] for row in rows if row.startswith('0::')]
 need(len(unified) == 1, 'One actual unified owned cgroup required')
 relative = Path(unified[0])
 need(relative.is_absolute() and '..' not in relative.parts and
      relative.name.endswith('.service'), 'Owned service cgroup required')
 cg = Path('/sys/fs/cgroup') / str(relative).lstrip('/')
 need((cg/'memory.max').read_text().strip() == str(PHYSICAL_BYTES),
      'Actual physical300GiB owned cgroup required')
 need((cg/'memory.swap.max').read_text().strip() == '0', 'No-swap owned cgroup required')
 limits = resource.getrlimit(resource.RLIMIT_AS)
 need(limits == (resource.RLIM_INFINITY, resource.RLIM_INFINITY),
      'Explicit unlimited parent virtual AS required; physical bound remains separate')
 events = {}
 for row in (cg/'memory.events').read_text().splitlines():
  key, value = row.split()
  need(key not in events and value.isdigit(), 'Strict actual memory event counters required')
  events[key] = int(value)
 need('oom' in events and 'oom_kill' in events, 'Actual owned OOM counters absent')
 return dict(cgroup=str(relative), physical_memory_max_bytes=PHYSICAL_BYTES,
             memory_swap_max_bytes=0, worker_virtual_as_policy=AS_POLICY,
             per_compiler_AS_bytes=None, memory_events=events)

def final_physical_guard(before):
 after = physical_guard()
 need(after['cgroup'] == before['cgroup'], 'Owned physical cgroup changed')
 return after

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--bank',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--memory-gib',type=int,required=True);ap.add_argument('--worker-virtual-as',choices=['unlimited'],required=True);a=ap.parse_args();physical_before=physical_guard();need(a.memory_gib==300,'physical planning declaration must match owned300GiB');need(not a.out.exists(),'fresh acceptance output required');start=time.monotonic()
 ctx,plan,result,inventory,peak=verify_bank(a.context,a.bank,'CanonicalW4EvolutionAudit','CANONICAL_W4_EVOLUTION_AUDIT_PASS claims=29 roots=38 ','CANONICAL_W4_EVOLUTION_AXIOMS ',38)
 need(plan.get('worker_virtual_as_policy')==AS_POLICY and plan.get('per_compiler_AS_bytes','missing')is None and plan.get('physical_memory_max_bytes')==PHYSICAL_BYTES,'Canonical compiler virtual/physical policy differs');need(all('--as=unlimited'in row['command']for row in result['commands']),'Actual compiler virtualAS policy differs');baseline=read_json(a.baseline);need(baseline.get('profile')=='canonical-w4','wrong immutable baseline profile');old=baseline['files'];need(type(old)is list and len(old)>=26,'complete original canonical baseline required');need(len({r['file']for r in old})==len(old),'duplicate baseline file')
 for row in old:need(sha(ROOT/row['file'])==row['sha256'],'old canonical file changed '+row['file'])
 expected={'CMSZeroSummation/v1','FapFourierNorm/v1','FapFourierNorm/v2','RHFiniteAffineIntervals/v1','RHFiniteAffineIntervals/v2','RHWeightedPopulation/v1'}
 present={str(Path(r['file']).parent.relative_to('IEANTN/Nodes'))for r in old if r['file'].startswith('IEANTN/Nodes/')}
 need(expected<=present,'baseline omits an original canonical family/version');a.out.mkdir();routes=entries(ROOT,a.context,ctx,a.bank.resolve(),NODES,a.out/'entry-routes')
 atomic(a.out/'CANONICAL_ACCEPTANCE.json',dict(status='PASS_CANONICAL_EXACT_CLAIMS_AND_DEPENDENCIES',scope='w4',claim_interfaces=29,node_versions=4,disjoint_entry_routes=len(routes),compiled_audit_roots=38,source_associated=True,source_cold=False,fresh_modules=len(plan['source_rows']),validated_inherited_modules=len(plan['accepted_dependencies']),proof_plan_sha256=sha(a.bank/'PLAN.json'),proof_result_sha256=sha(a.bank/'RESULT.json'),context_sha256=sha(a.context),baseline_sha256=sha(a.baseline),peak_proof_batch_process_RSS_kib=peak,physical_before=physical_before,physical_after=final_physical_guard(physical_before),worker_virtual_as_policy=AS_POLICY,per_compiler_AS_bytes=None,physical_memory_max_bytes=PHYSICAL_BYTES,oom_events_measured='actual owned cgroup before/after in physical_before/physical_after',resource_counter_scope='Owned verifier cgroup counters; proof bank has its own preserved compiler receipts.',proof_seconds=result['seconds'],validation_seconds=time.monotonic()-start,entry_point_routes=routes,validator_sha256=sha(Path(__file__)),python_optimization=sys.flags.optimize,official_Comparator_receipt=False,normal_cli_checks='Separate normalCLI fingerprint/graph/closure/pins/gen-challenges receipt remains required by final campaign packaging.'));print('PASS exact29 W4 canonical claims/dependencies; no officialComparator receipt')
if __name__=='__main__':main()
