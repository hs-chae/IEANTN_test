#!/usr/bin/env python3
"""Posthoc focused source recompilation against the exact assigned baseline/support."""
from pathlib import Path
import argparse,json,hashlib,os,re,subprocess,time,concurrent.futures,signal
D=Path('/data/ivy-rh-080-20261125');R=D/'network';S=R/'Solutions/RH080Study.v1';BASE=D/'baseline/frontier300-v1/run/compile';ASSIGNED=D/'ablation-representations-v1/E2/source';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--trial',required=True);p.add_argument('--prefix',required=True);p.add_argument('--root',action='append',required=True);p.add_argument('--theorem',action='append',default=[]);p.add_argument('--run',type=Path,required=True);a=p.parse_args();need(not a.run.exists(),'Fresh audit run required');data=json.loads((S/'ablation/followup/evidence/FOLLOWUP_REAUDIT_normal.json').read_text());trial=next(x for x in data['trials'] if x['id']==a.trial);pr=next(x for x in trial['timely_prefixes'] if Path(x['path']).name==a.prefix);P=Path(pr['path']);arm='V1' if '_V1-' in a.trial else 'V0';SUP=D/'ablation-followup-support'/arm
 C=json.loads(Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text());need(H(Path(C['compiler']))==C['compiler_sha256'],'Compiler bytes differ');pins=[]
 for q in (BASE/'source').rglob('*.lean'):
  assigned=ASSIGNED/q.relative_to(BASE/'source');need(assigned.is_file() and q.read_bytes()==assigned.read_bytes(),'Unassigned baseline source');pins.append(dict(module=str(q.relative_to(BASE/'source')),sha256=H(q)))
 for q in (SUP/'source').rglob('*.lean'):
  old=BASE/'source'/q.relative_to(SUP/'source')
  if old.is_file():need(old.read_bytes()==q.read_bytes(),'Assigned support/baseline source collision')
 a.run.mkdir(parents=True);src=a.run/'source';obj=a.run/'objects';logs=a.run/'logs';src.mkdir();obj.mkdir();logs.mkdir()
 for bank in [BASE/'objects',SUP/'objects']:
  for q in bank.rglob('*'):
   if q.is_file():
    target=obj/q.relative_to(bank);target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():target.unlink()
    os.link(q,target)
 own={}
 for row in pr['files']:
  q=P/row['file'];need(H(q)==row['sha256'],'Locked submitted source changed')
  if q.suffix=='.lean':(src/q.name).write_bytes(q.read_bytes());own[q.stem]=q
 order=[];seen=set()
 def visit(m):
  if m in seen:return
  seen.add(m)
  if m not in own:
   if m.startswith(('Mathlib','Lean.','Init','Std','Batteries','Aesop','Qq')):return
   need((obj/(m.replace('.','/')+'.olean')).is_file(),'Assigned provider unavailable '+m);return
  t=own[m].read_text()
  for line in t.splitlines():
   if line.startswith('import '):
    for z in line.split('--')[0][7:].split():visit(z)
  order.append(m)
 for m in a.root:visit(m)
 plan=dict(trial=a.trial,prefix=a.prefix,locked_sources=[dict(file=k,sha256=H(v)) for k,v in own.items()],compiled_submitted_modules=order,baseline_source_matches_assigned=len(pins),baseline_sources=pins,preexisting_baseline_bank=str(BASE/'objects'),preexisting_assigned_support=str(SUP/'objects'),full_fresh_application_closure=False,compiler=C['compiler'],compiler_sha256=H(Path(C['compiler'])),generic_lean_path=C['generic_lean_path'],controller_sha256=H(Path(__file__)))
 (a.run/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');env=os.environ.copy();env['LEAN_PATH']=str(obj)+':'+C['generic_lean_path'];rows=[];start=time.monotonic()
 def compile(m):
  source=src/(m+'.lean');target=obj/(m+'.olean');need(not target.exists(),'Submitted module shadows assigned bank');cmd=['/usr/bin/prlimit','--as='+str(64*2**30),'--','/usr/bin/time','-v',C['compiler'],'-j2','--root='+str(src),'-o',str(target),str(source)]
  t=time.monotonic()
  with (logs/(m+'.stdout')).open('wb') as out,(logs/(m+'.stderr')).open('wb') as err:
   process=subprocess.Popen(cmd,env=env,stdout=out,stderr=err,start_new_session=True)
   try:code=process.wait(timeout=240)
   except subprocess.TimeoutExpired:
    os.killpg(process.pid,signal.SIGTERM)
    try:process.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
    return dict(module=m,status='TIMEOUT_240S',returncode=None,seconds=time.monotonic()-t,command=cmd)
   run=type('ReturnCode',(),{'returncode':code})()
  return dict(module=m,status='PASS' if run.returncode==0 else 'FAIL',returncode=run.returncode,seconds=time.monotonic()-t,command=cmd,source_sha256=H(source),stdout_sha256=H(logs/(m+'.stdout')),stderr_sha256=H(logs/(m+'.stderr')),object_sha256=H(target) if target.is_file() else None)
 for m in order:
  row=compile(m);rows.append(row)
  if row['status']!='PASS':break
 if all(x['status']=='PASS' for x in rows) and len(rows)==len(order) and a.theorem:
  roots='#['+','.join('`'+x for x in a.theorem)+']';imports='\n'.join('import '+m for m in a.root)
  audit='''import Lean
IMPORTS
open Lean Elab Command
private partial def uses : Expr → List (String × Bool)
 | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::uses b
 | .mdata _ b => uses b
 | _ => []
run_cmd do
 let env←getEnv
 for root in ROOTS do
  let some (.thmInfo t):=env.find? root | throwError "Missing actual theorem {root}"
  let axs←collectAxioms root
  unless axs.all (#[`propext,`Classical.choice,`Quot.sound].contains) do throwError "Unaccepted axiom {root}:{axs}"
  logInfo m!"ACTUAL_TYPE {root}: {t.type}"
  logInfo m!"ACTUAL_SOURCE_VALUE {Json.mkObj [("root",toJson root.toString),("axioms",toJson (axs.map Name.toString)),("parameters",toJson ((uses t.value).map fun (n,u)=>Json.mkObj [("name",toJson n),("used",toJson u)])),("actual_value_constants",toJson (t.value.getUsedConstants.map Name.toString))]}"
 logInfo "PASS_FOCUSED_SUBMITTED_THEOREM_AUDIT"
'''.replace('IMPORTS',imports).replace('ROOTS',roots)
  (src/'SubmittedAudit.lean').write_text(audit);rows.append(compile('SubmittedAudit'))
 success=all(x['status']=='PASS' for x in rows) and len(rows)==len(order)+(bool(a.theorem))
 result=dict(status='PASS_FOCUSED_SUBMITTED_SOURCE_AND_AXIOM_AUDIT' if success else 'FAIL_OR_INCOMPLETE_SUBMITTED_SOURCE',trial=a.trial,prefix=a.prefix,seconds=time.monotonic()-start,commands=rows,source_predicates_still_explicit=True,verification_scope='Independent POSTHOC focused recompilation of exact timely source, using exact pretrial assigned baseline/support providers. NOT a fresh complete application closure or evidence of original in-trial compiler invocation.',full_fresh_application_closure=False,source_first_PV_inferred=False,original_primary_outcomes_changed=False,plan_sha256=H(a.run/'PLAN.json'))
 (a.run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','trial','prefix','seconds']}));
 if not success:print((logs/(rows[-1]['module']+'.stdout')).read_text()[-3000:])
if __name__=='__main__':main()
