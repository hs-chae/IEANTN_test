#!/usr/bin/env python3
"""Verify all canonical-evolution source/compile routes and disjoint entry points.
This is local evidence, never an official Comparator receipt. No Python assert.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
NODES=['CMSZeroSummation.v1','FapFourierNorm.v2','RHFiniteAffineIntervals.v2']
MARKER='CANONICAL_EVOLUTION_AUDIT_PASS roots=9 '
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,d):
 need(not p.exists(),'fresh receipt required');q=p.with_name('.'+p.name+'.tmp')
 with q.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 try:os.link(q,p)
 finally:q.unlink()
def imports(p):return[n for l in p.read_text().splitlines()if l.startswith('import ')for n in l[7:].split('--',1)[0].split()]
def clean(out,err,allow_sorry=False):
 text=out.read_text()+err.read_text();need(not re.search(r'PANIC|\berror(?:\(|:)',text),'compiler diagnostic rejected')
 if not allow_sorry:need('sorryAx'not in text and 'declaration uses'not in text,'proof admission rejected')
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--bank',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'fresh output required');started=time.monotonic();ctx=json.loads(a.context.read_text());need(sha(Path(ctx['compiler']))==ctx['compiler_sha256'],'compiler changed');bank=a.bank.resolve(strict=True);plan=json.loads((bank/'PLAN.json').read_text());result=json.loads((bank/'RESULT.json').read_text());need(plan['context_sha256']==sha(a.context),'context differs');need(plan['roots']==['CanonicalEvolutionAudit'],'wrong selected proof root');need(result['status']=='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY','proof batch incomplete');rows=plan['source_rows'];need(len({r['module']for r in rows})==len(rows),'collapsed fresh identities');commands={r['module']:r for r in result['commands']};need(set(commands)=={r['module']for r in rows}and len(commands)==len(result['commands']),'missing or duplicate actual compiler route');inventory={};peak=0
 for r in rows:
  n=r['module'];receipt=bank/(n+'.COMPILED.json');d=json.loads(receipt.read_text());need(d==commands[n]and d['exitcode']==0,'failed actual compiler child '+n);origin=Path(r['origin']);snapshot=Path(r['snapshot']);obj=bank/'objects'/(n.replace('.','/')+'.olean');need(sha(origin)==sha(snapshot)==r['source_sha256'],'current/frozen source differs '+n);need(sha(obj)==d['object_sha256'],'object differs '+n);need(d['command'][-6:]==[ctx['compiler'],'-j2','--root='+str(bank/'source'),'-o',str(obj),str(snapshot)],'actual compiler command differs '+n)
  for ext,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('time','time_sha256')]:need(sha(bank/'logs'/(n+'.'+ext))==d[key],'actual child log differs '+n)
  clean(bank/'logs'/(n+'.stdout'),bank/'logs'/(n+'.stderr'));tm=(bank/'logs'/(n+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm);need(len(rss)==1 and 'Command terminated by signal'not in tm,'resource/signal failure '+n);peak=max(peak,int(rss[0]));inventory[n]=origin
 for r in plan['accepted_dependencies']:
  n=r['module'];need(n not in inventory,'duplicate application module '+n);rp=Path(r['receipt']);need(sha(rp)==r['receipt_sha256'],'accepted dependency receipt changed '+n);d=json.loads(rp.read_text());origin=Path(r['source_origin']);need(d['exitcode']==0 and sha(origin)==sha(Path(r['snapshot']))==r['source_sha256'],'accepted dependency failed/source differs '+n);need(sha(bank/'objects'/(n.replace('.','/')+'.olean'))==r['object_sha256']==d['object_sha256'],'accepted dependency object differs '+n);inventory[n]=origin
 reached=set();active=set()
 def visit(n):
  if n in reached or n.split('.')[0]in GENERIC:return
  need(n in inventory,'missing actual application import '+n);need(n not in active,'cycle');active.add(n)
  for child in imports(inventory[n]):visit(child)
  active.remove(n);reached.add(n)
 visit('CanonicalEvolutionAudit');need(reached==set(inventory),'actual import closure differs');audit=(bank/'logs/CanonicalEvolutionAudit.stdout').read_text();need(audit.count(MARKER)==1 and audit.count('CANONICAL_EVOLUTION_AXIOMS ')==9,'compiled type/dependency/axiom audit incomplete')
 baseline=json.loads(a.baseline.read_text());old=baseline.get('old_v1_baseline',baseline.get('files'));need(isinstance(old,list)and len(old)==23,'exact original23 baseline required')
 for r in old:need(sha(ROOT/r['file'])==r['sha256'],'originalv1changed '+r['file'])
 for node in NODES:
  p=ROOT/'Solutions'/node;need((p/'lean-toolchain').read_bytes()==(ROOT/'lean-toolchain').read_bytes(),'Solution toolchain differs');need(all(not n.endswith('.Challenge')for n in imports(p/'Solution.lean')),'Solution imports Challenge')
  comparator=json.loads((p/'comparator.json').read_text());names={'CMSZeroSummation.v1':['partial_summation'],'FapFourierNorm.v2':['l1_bound'],'RHFiniteAffineIntervals.v2':['interval_08_full','interval_074_full','interval_075_full','interval_0777_small']}[node];need(comparator['challenge_module']=='IEANTN.Nodes.'+node+'.Challenge'and comparator['solution_module']=='Solution','Comparator module selection differs');need(comparator['theorem_names']==[node+'.challenge_'+n for n in names],'Comparator theorem coverage differs');need(set(comparator['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},'Comparator axiom policy differs')
 a.out.mkdir(parents=True);routes=[];env=dict(os.environ,LEAN_PATH=str(bank/'objects')+':'+ctx['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
 for node in NODES:
  family,version=node.split('.');routespecs=[('solution',ROOT/'Solutions'/node/'Solution.lean','Solution'),('challenge',ROOT/'IEANTN/Nodes'/family/version/'Challenge.lean','IEANTN.Nodes.'+family+'.'+version+'.Challenge')]
  for kind,origin,module in routespecs:
   run=a.out/(node+'-'+kind);source=run/'source';obj=run/'objects'/(module.replace('.','/')+'.olean');snapshot=source/(module.replace('.','/')+'.lean');snapshot.parent.mkdir(parents=True);obj.parent.mkdir(parents=True);snapshot.write_bytes(origin.read_bytes());out=run/'stdout';err=run/'stderr';tm=run/'time';command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(64*2**30),'--stack='+str(256*2**20),'--',ctx['compiler'],'-j2','--root='+str(source),'-o',str(obj),str(snapshot)]
   with out.open('xb')as o,err.open('xb')as e:p=subprocess.run(command,cwd=source,env=env,stdout=o,stderr=e)
   need(p.returncode==0 and obj.is_file(),'entry point failed '+node+' '+kind);clean(out,err,allow_sorry=kind=='challenge');routes.append(dict(node=node,kind=kind,module=module,command=command,exitcode=p.returncode,source_sha256=sha(origin),snapshot_sha256=sha(snapshot),object_sha256=sha(obj),stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm)))
 atomic(a.out/'RESULT.json',dict(status='PASS_LOCAL_CANONICAL_EVOLUTION_PROOFS_AND_DISJOINT_ENTRY_POINTS_NO_COMPARATOR',proof_result_sha256=sha(bank/'RESULT.json'),proof_plan_sha256=sha(bank/'PLAN.json'),context_sha256=sha(a.context),fresh_modules=len(rows),validated_dependencies=len(plan['accepted_dependencies']),compiled_theorem_roots=9,exact_generated_interfaces=6,original_v1_files_unchanged=23,peak_batch_Lean_rss_kib=peak,proof_seconds=result['seconds'],validation_seconds=time.monotonic()-started,oom_events=0,entry_point_routes=routes,validator_sha256=sha(Path(__file__)),python_optimization=sys.flags.optimize,official_Comparator_receipt=False));print('PASS local canonical proof/claim/source and disjoint Solution/Challenge gate; no Comparator receipt')
if __name__=='__main__':main()
