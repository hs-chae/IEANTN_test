#!/usr/bin/env python3
"""Optional bounded S13-only actual cold smoke; never a heavy N24/681 replay."""
import argparse,os,subprocess,sys,time
from pathlib import Path
from compact_contract import PACKAGE,sha,need,publish,check_project,load

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--project-root',type=Path,default=PACKAGE.parent);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--work',type=Path,required=True);a=ap.parse_args()
    need(not a.work.exists(),'Fresh small smoke directory required');project=a.project_root.resolve(strict=True);check_project(project)
    memberships=[x.split('::',1)[1]for x in Path('/proc/self/cgroup').read_text().splitlines()if x.startswith('0::')];need(len(memberships)==1 and memberships[0].endswith('.service'),'Owned small smoke unit required');cg=Path('/sys/fs/cgroup')/memberships[0].lstrip('/')
    need((cg/'memory.max').read_text().strip()==str(64*2**30)and(cg/'memory.swap.max').read_text().strip()=='0','Actual64GiB/noSwap small smoke policy required')
    available=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'));need(available>=320*2**30,'Preserve256GiB host reserve')
    before=(cg/'memory.events').read_text();a.work=a.work.absolute();a.work.mkdir(parents=True);source=a.work/'source-contract';candidate=source/'compact-candidate';run=a.work/'cold-kernel';bank=a.work/'format-bank'
    commands=[[sys.executable,str(PACKAGE/'tools/prepare_clean_compact_candidate.py'),'--stage','13','--work',str(source),'--project-root',str(project)],[sys.executable,'-u',str(project/'dual/reproduce_fft_dag_physical_v2.py'),'--context',str(a.context),'--candidate',str(candidate),'--run',str(run),'--workers','4','--worker-virtual-as','unlimited']]
    for mode,flags in enumerate([[],['-O'],['-OO']]):commands.append([sys.executable,*flags,str(PACKAGE/'tools/verify_fresh_compact.py'),'--run',str(run),'--context',str(a.context),'--candidate',str(candidate),'--output',str(a.work/f'accepted-{mode}.json'),'--project-root',str(project),'--proof-only-toy'])
    commands.append([sys.executable,str(PACKAGE/'tools/export_fresh_compact.py'),'--base',str(run),'--context',str(a.context),'--candidate',str(candidate),'--accepted',str(a.work/'accepted-0.json'),'--run',str(bank),'--project-root',str(project),'--toy'])
    pins=[dict(path=str(x),sha256=sha(x))for x in[Path(__file__),PACKAGE/'tools/compact_contract.py',PACKAGE/'tools/prepare_clean_compact_candidate.py',PACKAGE/'tools/derive_compact_candidate.py',PACKAGE/'tools/generate_compact_final_v2.py',PACKAGE/'tools/verify_fresh_compact.py',PACKAGE/'tools/export_fresh_compact.py']]
    publish(a.work/'PLAN.json',dict(status='PREPARED_SMALL_S13_ACTUAL_COLD_SMOKE_NOT_ACCEPTED',commands=commands,source_pins=pins,actual_physical_limit_bytes=64*2**30,actual_memory_events_before=before,source_cold_if_completed=True,N24_or681_replay_claimed=False));records=[];started=time.monotonic()
    try:
        for i,command in enumerate(commands):
            tick=time.monotonic()
            with(a.work/f'step-{i}.stdout').open('xb')as out,(a.work/f'step-{i}.stderr').open('xb')as err:r=subprocess.run(command,stdout=out,stderr=err)
            row=dict(index=i,command=command,returncode=r.returncode,seconds=time.monotonic()-tick,stdout_sha256=sha(a.work/f'step-{i}.stdout'),stderr_sha256=sha(a.work/f'step-{i}.stderr'));records.append(row);publish(a.work/f'step-{i}.RECEIPT.json',row);need(r.returncode==0 and not(a.work/f'step-{i}.stderr').read_bytes(),'Small clean smoke failed step '+str(i));print('COMPLETE',i,round(row['seconds'],3),flush=True)
        for pin in pins:need(sha(Path(pin['path']))==pin['sha256'],'Smoke runtime source changed')
        result=load(run/'RESULT.json');need(result['modules']==122 and result['audited_roots']==18,'Wrong small full cold claim scope')
        publish(a.work/'RESULT.json',dict(status='PASS_ACTUAL_SMALL_S13_REGENERATED_COMPACT122_COLD_KERNEL_GATES_EXPORT',records=records,seconds=time.monotonic()-started,actual_kernel_result_sha256=sha(run/'RESULT.json'),format_bank_result_sha256=sha(bank/'RESULT.json'),source_cold=True,source_first_C_PV_complete=False,N24_or681_fresh_replay_claimed=False,actual_memory_events_before=before,actual_memory_events_after=(cg/'memory.events').read_text()));print('PASS SMALL S13 COLD COMPACT ROUTE',flush=True)
    except BaseException as error:
        publish(a.work/'FAILURE.json',dict(status='NO_ACCEPTANCE_SMALL_S13_SMOKE',error=str(error),records=records,seconds=time.monotonic()-started,actual_memory_events_after=(cg/'memory.events').read_text()));raise
if __name__=='__main__':main()
