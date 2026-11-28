#!/usr/bin/env python3
"""Verify one completed normal S13 replay and optimization-safe new interfaces.

The mathematical checker itself was run once. No full optimized replay or N24
reproduction is inferred from command-only wrapper and independent-gate tests.
"""
import argparse,json,subprocess,sys
from pathlib import Path
from reproduce_dual import load,need,publish,sha
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','candidate','run','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh supplement destination required')
    r=load(a.run/'RESULT.json');p=load(a.run/'PLAN.json')
    need(r['stages']==13 and r['N']==8192 and r['modules']==120,
         'Exactly one completed bounded120-module S13 run required')
    a.out.mkdir();records=[];prepared=None
    for mode in range(3):
        flags=['-'+'O'*mode]if mode else[]
        wrapper=[sys.executable,*flags,str(HERE/'reproduce_fft_dag_physical_v2.py'),
            '--context',str(a.context),'--candidate',str(a.candidate),'--run',str(a.run),
            '--workers',str(p['workers']),'--worker-virtual-as','unlimited','--prepare-command']
        c=subprocess.run(wrapper,capture_output=True,text=True)
        need(c.returncode==0,'Actual optimized wrapper command preparation failed');command=json.loads(c.stdout)
        need(command['status']=='COMMAND_ONLY_NOT_EXECUTED_NOT_ACCEPTANCE'and command['virtual_AS_bytes']is None,
             'Command-only result was misclassified')
        need(command['command'][:2]==['prlimit','--as=unlimited'],'Wrong explicit inherited-AS command')
        if prepared is None:prepared=command
        else:need(command==prepared,'Optimization changed prepared original-checker command')
        accepted=a.out/('ACCEPTED-'+str(mode)+'.json')
        gate=[sys.executable,*flags,str(HERE/'verify_fft_dag_fresh_v3.py'),'--run',str(a.run),
            '--context',str(a.context),'--candidate',str(a.candidate),'--proof-only-toy','--output',str(accepted)]
        q=subprocess.run(gate,capture_output=True,text=True)
        (a.out/('gate-'+str(mode)+'.stdout')).write_text(q.stdout);(a.out/('gate-'+str(mode)+'.stderr')).write_text(q.stderr)
        need(q.returncode==0 and accepted.is_file(),'Independent completed-normal gate failed')
        bank=a.out/('export-'+str(mode));export=[sys.executable,*flags,str(HERE/'export_fft_dag_fresh_bank_v3.py'),
            '--base',str(a.run),'--context',str(a.context),'--candidate',str(a.candidate),
            '--accepted',str(accepted),'--run',str(bank),'--toy']
        e=subprocess.run(export,capture_output=True,text=True)
        (a.out/('export-'+str(mode)+'.stderr')).write_text(e.stderr)
        need(e.returncode==0 and (bank/'RESULT.json').is_file(),'Actual fresh normal format export failed')
        records.append(dict(mode=mode,wrapper_prepare_command=wrapper,prepared_command=command,
               gate_command=gate,gate_exitcode=q.returncode,gate_receipt_sha256=sha(accepted),
               export_command=export,export_exitcode=e.returncode,export_result_sha256=sha(bank/'RESULT.json')))
    publish(a.out/'RESULT.json',dict(status='PASS_ONE_ACTUAL_NORMAL_120_MODULE_COLD_REPLAY_WITH_3_MODE_INTERFACE_GATES',
          actual_full_normal_checker_replays=1,actual_full_optimized_checker_replays=0,
          independent_gate_modes=3,command_only_wrapper_modes=3,format_only_exports=3,
          stages=r['stages'],N=r['N'],modules=r['modules'],typed_standard_axiom_roots=r['audited_roots'],
          original_checker_seconds=r['seconds'],max_compiler_RSS_KiB=r['max_individual_RSS_KiB'],
          actual_normal_result_sha256=sha(a.run/'RESULT.json'),actual_normal_plan_sha256=sha(a.run/'PLAN.json'),
          records=records,wrapper_sha256=sha(HERE/'reproduce_fft_dag_physical_v2.py'),
          gate_sha256=sha(HERE/'verify_fft_dag_fresh_v3.py'),adapter_sha256=sha(HERE/'export_fft_dag_fresh_bank_v3.py'),
          harness_sha256=sha(Path(__file__)),actual_owned_cgroup_OOM_counters='NOT_MEASURED_FOR_BOUNDED_NORMAL_RUN',
          full_N24_fresh_replay=False,source_first_PV_claimed=False))
    print('PASS one normal120-module source-cold proof; new wrapper/gate/export all3 modes')
if __name__=='__main__':main()
