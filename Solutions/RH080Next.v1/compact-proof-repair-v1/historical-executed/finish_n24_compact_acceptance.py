#!/usr/bin/env python3
"""All actual production compact gates, then immutable mathematical-bank export."""
import hashlib,json,os,subprocess,sys,tempfile,time
from pathlib import Path
Q=Path(__file__).resolve().parent;D=Q.parent;OUT=Q/'n24-compact-independent-v1'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def publish(p,j):
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=p.parent)
    try:
        with os.fdopen(fd,'w')as f:json.dump(j,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,p)
    finally:Path(tmp).unlink()
def main():
    need(not OUT.exists(),'Fresh production independent-gate directory required');OUT.mkdir();started=time.monotonic();gate=Q/'verify_compact_final.py';exporter=Q/'export_compact_final_bank.py';run=Q/'run-s24-compact-v2';assembly=Q/'s24-compact-v2';ctx=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json')
    common=['--run',str(run),'--assembly',str(assembly),'--context',str(ctx),'--supervisor',str(D/'N24_COMPACT_SUPERVISOR_v2.json'),'--command-plan',str(D/'N24_COMPACT_EXECUTION_COMMAND_v2.json'),'--unit-policy',str(D/'N24_COMPACT_UNIT_COMMAND_v2.json'),'--page-policy',str(D/'N24_COMPACT_PROCESS_POLICY_v2.json')]
    commands=[[sys.executable,*flags,str(gate),*common,'--out',str(OUT/f'accepted-{mode}.json')]for mode,flags in enumerate([[],['-O'],['-OO']])]
    export=Q/'n24-compact-format-bank-v1';commands.append([sys.executable,str(exporter),'--base',str(run),'--assembly',str(assembly),'--context',str(ctx),'--accepted',str(OUT/'accepted-0.json'),'--run',str(export)])
    pins=[dict(path=str(p),sha256=sha(p))for p in[Path(__file__),gate,exporter,run/'PLAN.json',run/'RESULT.json',D/'N24_COMPACT_SUPERVISOR_v2.json']]
    publish(OUT/'PLAN.json',dict(status='PREPARED_ACTUAL_PRODUCTION_COMPACT_GATES_AND_FORMAT_EXPORT_NOT_ACCEPTED',commands=commands,source_pins=pins,math_providers=1035,actual_fresh_compiler_calls=5,diagnostic_import_probe_separate=True));records=[]
    try:
        for i,cmd in enumerate(commands):
            tick=time.monotonic()
            with(OUT/f'step-{i}.stdout').open('xb')as out,(OUT/f'step-{i}.stderr').open('xb')as err:r=subprocess.run(cmd,stdout=out,stderr=err)
            row=dict(index=i,command=cmd,returncode=r.returncode,seconds=time.monotonic()-tick,stdout_sha256=sha(OUT/f'step-{i}.stdout'),stderr_sha256=sha(OUT/f'step-{i}.stderr'));records.append(row);publish(OUT/f'step-{i}.RECEIPT.json',row);need(r.returncode==0 and not(OUT/f'step-{i}.stderr').read_bytes(),'Independent production gate/export failed step '+str(i));print('COMPLETE',i,round(row['seconds'],3),flush=True)
        for pin in pins:need(sha(Path(pin['path']))==pin['sha256'],'Frozen gate/execution evidence changed')
        export_result=json.loads((export/'RESULT.json').read_text());need(export_result['sources']==export_result['objects']==1035,'Wrong final math provider bank count')
        publish(OUT/'RESULT.json',dict(status='PASS_ACTUAL_N24_COMPACT_ALL3_INDEPENDENT_GATES_AND_IMMUTABLE1035_BANK',records=records,seconds=time.monotonic()-started,format_bank=str(export),format_bank_result_sha256=sha(export/'RESULT.json'),accepted_receipts=[dict(path=str(OUT/f'accepted-{mode}.json'),sha256=sha(OUT/f'accepted-{mode}.json'))for mode in[0,1,2]],actual_29_original_typed_roots_Std3=True,source_first_C_PV_complete=False,root_main_ANT_consumers_still_pending=True,plan_sha256=sha(OUT/'PLAN.json')))
        print('PASS N24 COMPACT INDEPENDENT1035 BANK',flush=True)
    except BaseException as error:
        publish(OUT/'FAILURE.json',dict(status='NO_ACCEPTANCE_COMPACT_GATE_EXPORT_FAILURE',error=str(error),records=records,seconds=time.monotonic()-started));raise
if __name__=='__main__':main()
