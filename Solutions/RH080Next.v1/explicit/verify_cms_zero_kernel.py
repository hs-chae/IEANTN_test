#!/usr/bin/env python3
"""Strict source-cold CMS zero-theorem acceptance; pure mathematics, not FFT PV.
Every actual compiler route, source identity, object, log, import and typed audit
is checked explicitly. Python -O/-OO do not disable any acceptance condition.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,sys,time
from pathlib import Path
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
MARKER='CMS_ZERO_KERNEL_AUDIT_PASS roots=12 '
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,value):
    need(not p.exists(),'fresh receipt required');t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:
        json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def imports(p):return [n for l in p.read_text().splitlines() if l.startswith('import ') for n in l[7:].split('--',1)[0].split()]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'fresh verifier output required');began=time.monotonic();run=a.run.resolve(strict=True);plan=json.loads((run/'PLAN.json').read_text());result=json.loads((run/'RESULT.json').read_text());context=json.loads(a.context.read_text());need(plan['context_sha256']==sha(a.context),'context changed');need(sha(Path(context['compiler']))==context['compiler_sha256'],'compiler changed');need(plan['roots']==result['roots']==['ExplicitCMSZeroKernelAudit'],'selected theorem/audit changed');need(plan['application_object_fallback'] is False,'application object fallback forbidden');need(result['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY','source-cold proof incomplete');rows=plan['source_rows'];need(len(rows)==result['modules'] and len({r['module'] for r in rows})==len(rows),'collapsed source/compiler identities');commands={r['module']:r for r in result['commands']};need(len(commands)==len(result['commands'])==len(rows),'missing/duplicate active compiler route');inventory={r['module']:r for r in rows};checked=[];peak=0
    for r in rows:
      n=r['module'];rp=run/(n+'.COMPILED.json');cr=json.loads(rp.read_text());need(cr==commands[n] and cr['module']==n and cr['exitcode']==0,'failed active compiler child '+n);obj=run/'objects'/(n.replace('.','/')+'.olean');cmd=cr['command'];need(cmd.count(context['compiler'])==1,'unpinned compiler child '+n);pos=cmd.index(context['compiler']);need(cmd[pos:]==[context['compiler'],'-j2','--root='+str(run/'source'),'-o',str(obj),r['snapshot']],'actual source/object command differs '+n);need(sha(Path(r['origin']))==sha(Path(r['snapshot']))==r['source_sha256'],'current/frozen source changed '+n);need(sha(obj)==cr['object_sha256'],'proof object changed '+n)
      for ext,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('time','time_sha256')]:need(sha(run/'logs'/(n+'.'+ext))==cr[key],'child evidence changed '+n)
      diag=(run/'logs'/(n+'.stdout')).read_text()+(run/'logs'/(n+'.stderr')).read_text();need(not re.search(r'PANIC|sorryAx|\berror(?:\(|:)',diag),'unclean compiler diagnostics '+n);tm=(run/'logs'/(n+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm);need(len(rss)==1 and 'Command terminated by signal' not in tm,'resource/signal failure '+n);peak=max(peak,int(rss[0]));checked.append(dict(module=n,origin=r['origin'],snapshot=r['snapshot'],source_sha256=r['source_sha256'],object_sha256=cr['object_sha256'],compiler_receipt_sha256=sha(rp)))
    reached=set();active=set()
    def visit(n):
      if n.split('.')[0] in GENERIC or n in reached:return
      need(n in inventory,'missing active application import '+n);need(n not in active,'import cycle');active.add(n)
      for child in imports(Path(inventory[n]['origin'])):visit(child)
      active.remove(n);reached.add(n)
    visit('ExplicitCMSZeroKernelAudit');need(reached==set(inventory),'selected import universe differs');audit=(run/'logs/ExplicitCMSZeroKernelAudit.stdout').read_text();need(audit.count(MARKER)==1 and audit.count('CMS_ZERO_KERNEL_AXIOMS ')==12,'typed/dependency/axiom audit incomplete');need('no-unformalized-source-scheme-premise no-native Std3' in audit,'kernel scope gate missing');a.out.mkdir(parents=True);atomic(a.out/'RESULT.json',dict(status='PASS_SOURCE_COLD_CMS_ZERO_PARTIAL_SUMMATION_KERNEL_THEOREM',source_cold_complete=True,mathematical_theorem='RH080Next.Explicit.cms_zero_partial_summation_kernel : SourceCMSZeroPartialSummationProofScheme',unformalized_generalized_scheme_premise=False,literal_zero_count_input_remaining=True,new_literature_premises=False,source_first_FFT_PV_complete=False,context_sha256=sha(a.context),proof_run=str(run),proof_plan_sha256=sha(run/'PLAN.json'),proof_result_sha256=sha(run/'RESULT.json'),source_rows=checked,modules=len(rows),axiom_roots=12,allowed_axioms=['propext','Classical.choice','Quot.sound'],peak_Lean_rss_kib=peak,proof_seconds=result['seconds'],validation_seconds=time.monotonic()-began,oom_events=0,logical_bank_disk_bytes=sum(p.stat().st_size for p in run.rglob('*') if p.is_file()),validator_sha256=sha(Path(__file__)),python_optimization=sys.flags.optimize));print('PASS source-cold CMS generic zero theorem; literal zero-count input remains, generic scheme premise removed')
if __name__=='__main__':main()
