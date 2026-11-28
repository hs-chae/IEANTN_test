#!/usr/bin/env python3
"""Reuse actual full normal/-O checks; full unchanged -OO concurrently; one export."""
import hashlib,json,os,signal,subprocess,sys,tempfile,time
from pathlib import Path
Q=Path(__file__).resolve().parent;D=Q.parent;OUT=Q/'n24-compact-parallel-v2';OLD=Q/'n24-compact-independent-v1';BANK=Q/'n24-compact-format-bank-v1'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def publish(p,j):
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=p.parent)
    try:
        with os.fdopen(fd,'w')as f:json.dump(j,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,p)
    finally:Path(tmp).unlink()
def load(p):
    def pairs(items):
        value={}
        for k,v in items:
            need(k not in value,'Duplicate JSON key');value[k]=v
        return value
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs)
def main():
    need(not OUT.exists(),'Fresh parallel orchestration required');need(not BANK.exists(),'Do not race existing export');OUT.mkdir();started=time.monotonic()
    gate=Q/'verify_compact_final.py';exporter=Q/'export_compact_final_bank.py';oldscript=Q/'finish_n24_compact_acceptance.py';oldplan=load(OLD/'PLAN.json')
    need(sha(gate)=='b1054ae8bb6b5ae23f73e3949470c9b84a0d35a9c165bcf709c890929b00ce2f'and sha(exporter)=='b1f7b10891a9fdb390bdd59f577c558311f58cd3558f2a7197e6215588166acc','Frozen exhaustive reader/exporter changed')
    command=list(oldplan['commands'][2]);need(command[:3]==[sys.executable,'-OO',str(gate)],'Unchanged actual full -OO invocation required')
    need(command[-2]=='--out','Expected exact acceptance-output argument');command[-1]=str(OUT/'accepted-2.json')
    exportcommand=list(oldplan['commands'][3]);need(exportcommand[-2:]==['--run',str(BANK)],'Frozen provider bank path differs')
    pins=[dict(path=str(x),sha256=sha(x))for x in[Path(__file__),gate,exporter,oldscript,OLD/'PLAN.json']]
    publish(OUT/'PLAN.json',dict(status='PREPARED_FULL_PARALLEL_OO_REUSE_ACTUAL_NORMAL_AND_O_NOT_ACCEPTED',OO_command=command,export_command=exportcommand,source_pins=pins,normal_receipt=str(OLD/'accepted-0.json'),O_receipt=str(OLD/'accepted-1.json'),same_full_checks=True,no_hash_caching=True,no_reader_or_exporter_changes=True))
    stopped=False;child=None
    try:
        with(OUT/'OO.stdout').open('xb')as out,(OUT/'OO.stderr').open('xb')as err:
            child=subprocess.Popen(command,stdout=out,stderr=err)
            while True:
                failure=OLD/'FAILURE.json';need(not failure.exists(),'Original serial pipeline failed; preserve failure')
                done=OLD/'step-1.RECEIPT.json'
                if done.is_file()and not stopped:
                    for mode in[0,1]:
                        receipt=load(OLD/f'step-{mode}.RECEIPT.json');accepted=load(OLD/f'accepted-{mode}.json')
                        need(receipt['returncode']==0 and receipt['command']==oldplan['commands'][mode]and accepted['status']=='PASS_INDEPENDENT_COMPACT_NUMERICAL_KERNEL_ONLY_NOT_C_PV','Actual completed original mode missing')
                    need(not(OLD/'accepted-2.json').exists()and not BANK.exists(),'Serial third mode/export reached acceptance; avoid duplicate export')
                    info=subprocess.run(['systemctl','--user','show','ivy-n24-compact-independent-v1.service','-p','MainPID','-p','ActiveState'],capture_output=True,text=True)
                    values=dict(line.split('=',1)for line in info.stdout.splitlines()if'='in line);pid=int(values.get('MainPID','0'));need(pid==1386920,'Only exact old coordinator may be stopped')
                    args=Path('/proc',str(pid),'cmdline').read_bytes().replace(b'\0',b' ').decode();need(str(oldscript)in args,'Old coordinator identity changed')
                    publish(OUT/'SERIAL_BOUNDARY_STOP_PLAN.json',dict(status='INTENTIONAL_RESOURCE_ORCHESTRATION_STOP_NOT_MATH_FAILURE',unit='ivy-n24-compact-independent-v1.service',actual_MainPID=pid,actual_argv=args,completed_modes=[0,1],completed_receipt_hashes={str(OLD/f'step-{m}.RECEIPT.json'):sha(OLD/f'step-{m}.RECEIPT.json')for m in[0,1]},reason='Preserve two full actual successes; third full check is unchanged parallel -OO. Stop only redundant serial third reader before any export.'))
                    stop=subprocess.run(['systemctl','--user','stop','ivy-n24-compact-independent-v1.service'],capture_output=True,text=True,timeout=45)
                    after=subprocess.run(['systemctl','--user','show','ivy-n24-compact-independent-v1.service','-p','MainPID','-p','ActiveState','-p','Result'],capture_output=True,text=True)
                    publish(OUT/'SERIAL_BOUNDARY_STOP_RESULT.json',dict(returncode=stop.returncode,stdout=stop.stdout,stderr=stop.stderr,actual_unit_after=after.stdout,old_original_receipts_unchanged=True,old_serial_RESULT_present=(OLD/'RESULT.json').exists()))
                    need(stop.returncode==0 and'MainPID=0'in after.stdout and not BANK.exists(),'Old serial unit not safely stopped before export');stopped=True;print('ORIGINAL_NORMAL_AND_O_COMPLETE_OLD_SERIAL_STOPPED',flush=True)
                code=child.poll()
                if stopped and code is not None:break
                time.sleep(.5)
            code=child.wait()
        oo=dict(command=command,returncode=code,stdout_sha256=sha(OUT/'OO.stdout'),stderr_sha256=sha(OUT/'OO.stderr'),accepted_sha256=sha(OUT/'accepted-2.json')if(OUT/'accepted-2.json').exists()else None)
        publish(OUT/'OO.RECEIPT.json',oo);need(code==0 and not(OUT/'OO.stderr').read_bytes(),'Full unchanged parallel -OO failed')
        paths=[OLD/'accepted-0.json',OLD/'accepted-1.json',OUT/'accepted-2.json'];values=[load(x)for x in paths]
        fixed=['status','toy_only','stage','N','norm_numerator','numerical_source_cold_leaves','fresh_mathematical_proof_modules','math_bank_modules','actual_fresh_compiler_calls','typed_original_roots','root_axioms','plan_sha256','result_sha256','assembly_sha256','validator_sha256','actual_resource_evidence']
        for value in values:
            need(all(value[k]==values[0][k]for k in fixed),'Actual full-check scopes differ');need(value['math_bank_modules']==1035 and value['typed_original_roots']==29 and value['toy_only']is False,'Wrong production scope')
        need(not BANK.exists(),'Export path must remain fresh');tick=time.monotonic()
        with(OUT/'export.stdout').open('xb')as out,(OUT/'export.stderr').open('xb')as err:r=subprocess.run(exportcommand,stdout=out,stderr=err)
        rec=dict(command=exportcommand,returncode=r.returncode,seconds=time.monotonic()-tick,stdout_sha256=sha(OUT/'export.stdout'),stderr_sha256=sha(OUT/'export.stderr'));publish(OUT/'EXPORT.RECEIPT.json',rec);need(r.returncode==0 and not(OUT/'export.stderr').read_bytes(),'Unchanged exporter failed')
        for pin in pins:need(sha(Path(pin['path']))==pin['sha256'],'Frozen reader/exporter/orchestration changed')
        result=load(BANK/'RESULT.json');need(result['sources']==result['objects']==1035,'Wrong immutable provider count')
        publish(OUT/'RESULT.json',dict(status='PASS_ACTUAL_FULL_NORMAL_O_OO_COMPACT_GATES_AND1035_IMMUTABLE_BANK',accepted_receipts=[dict(path=str(x),sha256=sha(x))for x in paths],old_serial_two_completed_modes_preserved=True,old_serial_third_reader_intentionally_stopped_not_mathematical_failure=True,all_three_full_exhaustive_readers_same_source=True,unchanged_exporter_invoked_once=True,format_bank=str(BANK),format_bank_result_sha256=sha(BANK/'RESULT.json'),source_first_C_PV_complete=False,root_main_ANT_consumers_pending=True,seconds=time.monotonic()-started,plan_sha256=sha(OUT/'PLAN.json')))
        print('PASS FULL THREE MODE COMPACT BANK',flush=True)
    except BaseException as error:
        if child is not None and child.poll()is None:child.terminate();child.wait()
        publish(OUT/'FAILURE.json',dict(status='NO_ACCEPTANCE_PARALLEL_GATE_ORCHESTRATION',error=str(error),old_serial_stopped=stopped,seconds=time.monotonic()-started));raise
if __name__=='__main__':main()
