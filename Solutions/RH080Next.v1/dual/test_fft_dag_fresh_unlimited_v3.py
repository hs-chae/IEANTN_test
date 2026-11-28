#!/usr/bin/env python3
"""Actually replay the unchanged S13 checker through the new unlimited-AS wrapper.

No full N24 replay or production resource acceptance is claimed by these tests.
"""
import argparse,json,subprocess,sys,time
from pathlib import Path
from reproduce_dual import load,need,publish,sha
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','candidate','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh controls required')
    need(load(a.candidate/'PLAN.json')['stages']==13,'Actual bounded S13 candidate required')
    a.out.mkdir();records=[];started=time.monotonic()
    for mode in range(3):
        flags=['-'+'O'*mode]if mode else[];run=a.out/('fresh-'+str(mode))
        command=[sys.executable,*flags,str(HERE/'reproduce_fft_dag_physical_v2.py'),
            '--context',str(a.context),'--candidate',str(a.candidate),'--run',str(run),
            '--workers','1','--worker-virtual-as','unlimited']
        prepared=subprocess.run([*command,'--prepare-command'],capture_output=True,text=True)
        need(prepared.returncode==0,'Wrapper command preparation failed');proposal=json.loads(prepared.stdout)
        need(proposal['virtual_AS_bytes']is None and proposal['command'][:2]==['prlimit','--as=unlimited'],
             'Wrapper did not prescribe explicit unlimited virtual AS')
        with (a.out/('fresh-'+str(mode)+'.stdout')).open('xb')as f,(a.out/('fresh-'+str(mode)+'.stderr')).open('xb')as g:
            actual=subprocess.run(command,stdout=f,stderr=g)
        need(actual.returncode==0 and (run/'RESULT.json').is_file(),'Actual original fresh S13 checker failed')
        result=load(run/'RESULT.json');need(result['stages']==13,'Unexpected nonbounded workload')
        accepted=a.out/('accepted-'+str(mode)+'.json')
        gate=[sys.executable,*flags,str(HERE/'verify_fft_dag_fresh_v3.py'),'--run',str(run),
            '--context',str(a.context),'--candidate',str(a.candidate),'--proof-only-toy','--output',str(accepted)]
        p=subprocess.run(gate,capture_output=True,text=True)
        (a.out/('gate-'+str(mode)+'.stdout')).write_text(p.stdout);(a.out/('gate-'+str(mode)+'.stderr')).write_text(p.stderr)
        need(p.returncode==0 and accepted.is_file(),'Actual fresh mathematical gate rejected')
        export=a.out/('export-'+str(mode));cmd=[sys.executable,*flags,str(HERE/'export_fft_dag_fresh_bank_v3.py'),
             '--base',str(run),'--context',str(a.context),'--candidate',str(a.candidate),
             '--accepted',str(accepted),'--run',str(export),'--toy']
        e=subprocess.run(cmd,capture_output=True,text=True)
        (a.out/('export-'+str(mode)+'.stderr')).write_text(e.stderr)
        need(e.returncode==0 and (export/'RESULT.json').is_file(),'Fresh format-only adapter failed')
        records.append(dict(mode=mode,command=command,prepared_command=proposal['command'],modules=result['modules'],
             returncode=actual.returncode,result_sha256=sha(run/'RESULT.json'),gate_command=gate,
             acceptance_sha256=sha(accepted),export_command=cmd,export_sha256=sha(export/'RESULT.json')))
        print('PASS actual fresh unlimited-AS S13 mode',mode,flush=True)
    publish(a.out/'RESULT.json',dict(status='PASS_3_ACTUAL_FRESH_S13_WRAPPER_REPLAYS_ALL_MODES',
            records=records,seconds=time.monotonic()-started,wrapper_sha256=sha(HERE/'reproduce_fft_dag_physical_v2.py'),
            gate_sha256=sha(HERE/'verify_fft_dag_fresh_v3.py'),adapter_sha256=sha(HERE/'export_fft_dag_fresh_bank_v3.py'),
            harness_sha256=sha(Path(__file__)),N24_full_cold_replay_executed=False,
            production_resource_gate_exercised=False,new_source_first_PV_claimed=False))
if __name__=='__main__':main()
