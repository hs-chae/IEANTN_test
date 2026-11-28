#!/usr/bin/env python3
"""Independently check every source-cold initializer proof route and native control.
Acceptance does not depend on assert/__debug__, and remains active under -O/-OO.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path

def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,value):
    need(not p.exists(),'fresh receipt required');t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--native',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(not a.out.exists(),'fresh experiment-owned output required');began=time.monotonic();run=a.run.resolve(strict=True)
    plan=json.loads((run/'PLAN.json').read_text());result=json.loads((run/'RESULT.json').read_text());context=json.loads(a.context.read_text())
    need(plan['context_sha256']==sha(a.context),'pinned dependency context changed')
    need(plan['roots']==result['roots']==['ExplicitFFTRootAudit'],'different final theorem/audit roots')
    need(plan['application_object_fallback'] is False,'application object fallback forbidden')
    need(result['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY','source-cold closure incomplete')
    rows=plan['source_rows'];need(len(rows)==result['modules'] and len(rows)>130,'complete selected import closure required')
    need(len({r['module'] for r in rows})==len(rows) and len({(r['origin'],r['module']) for r in rows})==len(rows),'collapsed compiler/written-source identities')
    need(sha(Path(context['compiler']))==context['compiler_sha256'],'pinned compiler changed')
    expected_commands={r['module']:r for r in result['commands']};need(len(expected_commands)==len(rows),'missing/duplicate actual compiler routes')
    accepted=[];peak=0
    for row in rows:
      n=row['module'];rp=run/(n+'.COMPILED.json');r=json.loads(rp.read_text());need(r['module']==n and r['exitcode']==0,'failed child '+n)
      need(expected_commands[n]==r,'root/child command receipts disagree '+n)
      command=r['command'];obj=run/'objects'/(n.replace('.','/')+'.olean');position=command.index(context['compiler']) if context['compiler'] in command else -1
      need(command.count(context['compiler'])==1 and position>=0 and command[position:]==[context['compiler'],'-j2','--root='+str(run/'source'),'-o',str(obj),row['snapshot']],'actual compiler source/object route changed '+n)
      need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'origin/frozen-source changed '+n)
      need(sha(obj)==r['object_sha256'],'accepted proof object changed '+n)
      for extension,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('time','time_sha256')]:need(sha(run/'logs'/(n+'.'+extension))==r[key],'changed child evidence '+n)
      diagnostics=(run/'logs'/(n+'.stdout')).read_text()+(run/'logs'/(n+'.stderr')).read_text();need(not any(x in diagnostics for x in ['PANIC','error:','sorryAx']),'unclean compiler output even if exit0 '+n)
      tm=(run/'logs'/(n+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm);need(len(rss)==1,'missing resource receipt '+n);peak=max(peak,int(rss[0]));need('Command terminated by signal' not in tm,'signal/resource failure '+n)
      accepted.append(dict(module=n,source_sha256=row['source_sha256'],object_sha256=r['object_sha256'],compiler_receipt_sha256=sha(rp)))
    audit=(run/'logs/ExplicitFFTRootAudit.stdout').read_text();marker='FFT_ROOT_SOURCE_AUDIT_PASS four-actual-C-files independently-parsed full-Call all-executions all-argument-orders ten-Taylor-iterations two-original-grids actual-integer-root same-512-allocation slice-preservation no-wrap temporary-lifetimes caller-frame Std3 final-ANT-connection-pending'
    need(audit.count(marker)==1 and audit.count('FFT_ROOT_SOURCE_AXIOMS ')==4,'incomplete consumed source/math/axiom audit')
    native=json.loads((a.native/'RESULT.json').read_text());need(native['status']=='PASS_NATIVE_ROOT_CORROBORATION_AND_WRONG_SOURCE_CONTROLS_ONLY' and native['proof'] is False and native['source_first_PV_complete'] is False,'native tests must not be relabeled proof')
    need(native['seed']==0x080B007 and len(native['cases'])==16 and len(native['rows'])==4,'changed native parameters/routes')
    need({c['n'] for c in native['cases']}=={131072,16777216},'both original grids required')
    need(sha(Path(native['compiler']))==native['compiler_sha256'],'native compiler changed')
    actual=[]
    for row,expected_name in zip(native['rows'],['w4_fft.c','fap_fft.c','w4_fft_recursive.c','fap_fft_recursive.c']):
      need(Path(row['concrete_source']).name==expected_name and row['cases']==16,'wrong native source route')
      need(sha(Path(row['concrete_source']))==sha(Path(row['snapshot']))==row['source_sha256'] and sha(Path(row['formal_source']))==row['formal_sha256'],'native/formal source association changed')
      harness=a.native/(expected_name+'.test.c');exe=a.native/(expected_name+'.test');need(sha(harness)==row['harness_sha256'] and sha(exe)==row['executable_sha256'],'native harness/executable changed')
      replay=subprocess.run([str(exe)],capture_output=True,text=True);need(replay.returncode==0 and replay.stderr=='' and hashlib.sha256(replay.stdout.encode()).hexdigest()==row['output_sha256'],'native actual rerun failed')
      need(len(row['mutations'])==4,'missing wrong-source controls')
      for m in row['mutations']:
        mutated=a.native/(expected_name+'.'+m['name']+'.c');mh=a.native/(expected_name+'.'+m['name']+'.test.c');me=a.native/(expected_name+'.'+m['name']+'.test')
        need(sha(mutated)==m['source_sha256'] and sha(mh)==m['harness_sha256'],'wrong-source fixture changed')
        need(mutated.read_text()==Path(row['snapshot']).read_text().replace(m['original_fragment'],m['mutated_fragment']),'wrong-source recipe differs')
        observed=subprocess.run([str(me)],capture_output=True,text=True);need(observed.returncode==m['exitcode'] and observed.returncode>0,'mutation must be a normal semantic mismatch, not a signal')
      actual.append(dict(source=expected_name,source_sha256=row['source_sha256'],native_returncode=replay.returncode,controls=4))
    a.out.mkdir(parents=True)
    atomic(a.out/'RESULT.json',dict(status='PASS_INITIALIZE_ROOT_SOURCE_EXECUTION_CORRECTNESS_CONTRACT_ONLY',source_to_AST_execution_correctness_contract_complete=True,source_first_PV_complete=False,final_ANT_connection_pending=True,whole_FFT_norm_PV_complete=False,source_cold_run=str(run),proof_receipt_sha256=sha(run/'RESULT.json'),plan_sha256=sha(run/'PLAN.json'),context_sha256=sha(a.context),modules=accepted,native_receipt_sha256=sha(a.native/'RESULT.json'),native_actual_rechecks=actual,validator_sha256=sha(Path(__file__)),python=sys.version,python_optimization=sys.flags.optimize,peak_Lean_rss_kib=peak,proof_seconds=result['seconds'],validation_seconds=time.monotonic()-began,oom_events=0,disk_bytes=sum(p.stat().st_size for p in run.rglob('*') if p.is_file()),trust='The selected C operational model and LP64/ULL64 ABI, pinned compiler/core runtime, OS and hardware. Caller proves actual typed allocation/layout. No application initialization, successful effects, exact root outputs or final ANT bound is assumed.',scope='Two actual original grids, all ten source Taylor iterations, actual four preserved C source syntaxes, exact root integer model, all permitted Calls/order/termination cases, shared512 root/work slices and physical preservation outside work80/root12. Standalone helper contract; full FFT/main/ANT consumption remains pending.'))
    print('PASS complete initializer source/execution/correctness contract; final ANT connection pending')
if __name__=='__main__':main()
