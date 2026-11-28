#!/usr/bin/env python3
"""Strict independent source-quad receipt, import-closure and native rechecks.
Acceptance stays active under normal Python, -O and -OO. Source-associated and
source-cold replays are distinguished; neither alone completes final ANT PV.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
AUDIT='FFT_QUAD_AUDIT_PASS two-original-recursive-C-sources exact400and2520inputs actual-seven-statement-row whole-loop every-execution source-selector-to-existing-integer-quad Fap-extra100 W4-unscaled no-wrap real-memory caller-frame Std3 main-ANT-connection-pending'
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
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',required=True,type=Path);ap.add_argument('--run',required=True,type=Path);ap.add_argument('--native',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args();need(not a.out.exists(),'fresh verification output required');began=time.monotonic();run=a.run.resolve(strict=True);plan=json.loads((run/'PLAN.json').read_text());result=json.loads((run/'RESULT.json').read_text());context=json.loads(a.context.read_text())
    need(plan['context_sha256']==sha(a.context),'context changed');need(sha(Path(context['compiler']))==context['compiler_sha256'],'compiler changed');need(plan['roots']==result['roots']==['ExplicitFFTQuadAudit'],'selected theorem/audit changed');need(plan['application_object_fallback'] is False,'application object fallback forbidden')
    cold=result['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY';need(cold or result['status']=='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY','incomplete proof replay');fresh=plan['source_rows'];need(len(fresh)==result['modules'],'fresh module coverage mismatch');accepted=[] if cold else plan['accepted_dependencies'];rows={};peak=0;checked=[]
    commands={r['module']:r for r in result['commands']};need(len(commands)==len(result['commands'])==len(fresh),'missing or duplicate compiler child')
    for r in fresh:
      n=r['module'];need(n not in rows,'collapsed source/compiler identity');rows[n]=dict(module=n,origin=r['origin'],snapshot=r['snapshot'],source_sha256=r['source_sha256'],fresh=True)
      rp=run/(n+'.COMPILED.json');cr=json.loads(rp.read_text());need(cr==commands[n] and cr['module']==n and cr['exitcode']==0,'failed or inconsistent active child '+n);obj=run/'objects'/(n.replace('.','/')+'.olean');cmd=cr['command'];need(cmd.count(context['compiler'])==1,'unpinned compiler route '+n);pos=cmd.index(context['compiler']);need(cmd[pos:]==[context['compiler'],'-j2','--root='+str(run/'source'),'-o',str(obj),r['snapshot']],'source/object/compiler command differs '+n)
      need(sha(Path(r['origin']))==sha(Path(r['snapshot']))==r['source_sha256'],'current/frozen source changed '+n);need(sha(obj)==cr['object_sha256'],'compiled object changed '+n)
      for ext,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('time','time_sha256')]:need(sha(run/'logs'/(n+'.'+ext))==cr[key],'child evidence changed '+n)
      text=(run/'logs'/(n+'.stdout')).read_text()+(run/'logs'/(n+'.stderr')).read_text();need(not re.search(r'PANIC|sorryAx|\berror(?:\(|:)',text),'compiler diagnostics rejected '+n);tm=(run/'logs'/(n+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm);need(len(rss)==1 and 'Command terminated by signal' not in tm,'missing resource or signal failure '+n);peak=max(peak,int(rss[0]));checked.append(dict(module=n,source_origin=r['origin'],source_sha256=r['source_sha256'],snapshot=r['snapshot'],compiler_receipt=str(rp),compiler_receipt_sha256=sha(rp),object_sha256=cr['object_sha256'],fresh=True))
    for r in accepted:
      n=r['module'];need(n not in rows,'collapsed transitive source identity');rows[n]=dict(module=n,origin=r['source_origin'],snapshot=r['snapshot'],source_sha256=r['source_sha256'],fresh=False);rp=Path(r['receipt']);cr=json.loads(rp.read_text());obj=run/'objects'/(n.replace('.','/')+'.olean');need(sha(rp)==r['receipt_sha256'] and cr['module']==n and cr['exitcode']==0,'reused compiler receipt changed '+n);need(sha(Path(r['source_origin']))==sha(Path(r['snapshot']))==r['source_sha256'],'reused source changed '+n);need(sha(obj)==r['object_sha256']==cr['object_sha256'],'reused object changed '+n);need(cr['command'].count(context['compiler'])==1,'reused compiler pin differs '+n);checked.append(dict(module=n,source_origin=r['source_origin'],source_sha256=r['source_sha256'],snapshot=r['snapshot'],compiler_receipt=str(rp),compiler_receipt_sha256=sha(rp),object_sha256=r['object_sha256'],fresh=False))
    # Reconstruct coverage from the actual current pinned source import graph.
    reached=set();active=set()
    def visit(n):
      if n.split('.')[0] in GENERIC or n in reached:return
      need(n in rows,'missing active application import '+n);need(n not in active,'application import cycle');active.add(n)
      for child in imports(Path(rows[n]['origin'])):visit(child)
      active.remove(n);reached.add(n)
    visit('ExplicitFFTQuadAudit');need(reached==set(rows),'recorded import closure differs from the actual selected theorem')
    audit=(run/'logs/ExplicitFFTQuadAudit.stdout').read_text();need(audit.count(AUDIT)==1 and audit.count('FFT_QUAD_AXIOMS [propext, Classical.choice, Quot.sound]')==1,'consumed-path/axiom audit incomplete')
    native=json.loads((a.native/'RESULT.json').read_text());need(native['status']=='PASS_NATIVE_QUAD_CORROBORATION_AND_WRONG_SOURCE_CONTROLS_ONLY' and native['proof'] is False and native['source_first_PV_complete'] is False,'native tests must remain tests');need(native['seed']==0x080A0AD and len(native['rows'])==4,'native routes or seed changed');need(sha(Path(native['compiler']))==native['compiler_sha256'],'native compiler changed');need(native['script_sha256']==sha(Path(__file__).with_name('reproduce_fft_quad_native.py')),'native generator changed');native_checks=[]
    for r,name in zip(native['rows'],['w4_fft.c','fap_fft.c','w4_fft_recursive.c','fap_fft_recursive.c']):
      fap=name.startswith('fap');need(Path(r['concrete_source']).name==name and r['cases']==8 and r['count']==(400 if fap else 2520) and r['grid']==(131072 if fap else 16777216) and r['Fap_extra100'] is fap,'changed native source/profile');source=Path(r['concrete_source']);snapshot=a.native/name;need(sha(source)==sha(snapshot)==r['source_sha256'] and sha(Path(r['formal_source']))==r['formal_sha256'],'native/formal source association changed');data=Path(r['input']);need(sha(data)==r['input_sha256'],'locked native input changed');m=re.search(r'^def encoded : List Nat := \[([0-9, ]+)\]$',data.read_text(),re.M);need(m is not None,'input representation changed');nodes=[int(x) for x in m.group(1).split(', ')];need(len(nodes)==r['count'],'input count differs');raw=sum(20*j*j*abs(e-10**16) for j,e in enumerate(nodes));need(str(raw)==r['raw_quad'] and str(raw*(100 if fap else 1))==r['scaled_quad'],'native integer specification differs');harness=a.native/(name+'.test.c');exe=a.native/(name+'.test');need(sha(harness)==r['harness_sha256'] and sha(exe)==r['executable_sha256'],'native executable/harness changed');actual=subprocess.run([str(exe)],capture_output=True,text=True);need(actual.returncode==0 and actual.stdout=='OK\n'*8 and actual.stderr=='','native actual rerun failed')
      expected={'factor20-to21','negative-branch-zero','add-only-one-word','truncated-loop'}|({'Fap-scale100-to99'} if fap else set());need({x['name'] for x in r['mutations']}==expected and len(r['mutations'])==len(expected),'missing mutation controls');start,end=r['segment_byte_start'],r['segment_byte_end'];original=snapshot.read_text();frag=original[start:end];need(hashlib.sha256(frag.encode()).hexdigest()==r['extracted_segment_sha256'],'actual segment changed')
      for mut in r['mutations']:
        ms=a.native/(name+'.'+mut['name']+'.c');mh=a.native/(name+'.'+mut['name']+'.test.c');me=a.native/(name+'.'+mut['name']+'.test');need(sha(ms)==mut['source_sha256'] and sha(mh)==mut['harness_sha256'],'mutation artifact changed');need(frag.count(mut['original_fragment'])==1 and ms.read_text()==original[:start]+frag.replace(mut['original_fragment'],mut['mutated_fragment'])+original[end:],'source mutation recipe differs');observed=subprocess.run([str(me)],capture_output=True,text=True);need(observed.returncode==mut['exitcode'] and observed.returncode>0,'mutation must fail normally, not by signal')
      native_checks.append(dict(source=name,source_sha256=r['source_sha256'],cases=8,mutations=len(expected)))
    a.out.mkdir(parents=True);atomic(a.out/'RESULT.json',dict(status='PASS_QUAD_SOURCE_EXECUTION_CORRECTNESS_CONTRACT_ONLY',source_to_AST_execution_correctness_contract_complete=True,source_cold_complete=cold,source_first_PV_complete=False,final_ANT_connection_pending=True,proof_run=str(run),proof_result_sha256=sha(run/'RESULT.json'),proof_plan_sha256=sha(run/'PLAN.json'),context_sha256=sha(a.context),fresh_modules=len(fresh),reused_modules=len(accepted),source_closure=checked,native_receipt_sha256=sha(a.native/'RESULT.json'),native_rechecks=native_checks,validator_sha256=sha(Path(__file__)),python=sys.version,python_optimization=sys.flags.optimize,peak_fresh_Lean_rss_kib=peak,proof_seconds=result['seconds'],validation_seconds=time.monotonic()-began,oom_events=0,logical_disk_bytes=sum(p.stat().st_size for p in run.rglob('*') if p.is_file())))
    print('PASS actual quad source/execution/correctness contract; final main/ANT connection pending')
if __name__=='__main__':main()
