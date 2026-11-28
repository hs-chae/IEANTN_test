#!/usr/bin/env python3
"""Portable ORIGINAL producer then source-only compact derivation; still untrusted."""
import argparse,sys,subprocess,time
from pathlib import Path
from compact_contract import PACKAGE,load,locked,sha,need,publish,check_project,validate_derived

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--stage',type=int,choices=[13,24],required=True);ap.add_argument('--work',type=Path,required=True);ap.add_argument('--project-root',type=Path,default=PACKAGE.parent);a=ap.parse_args()
    need(not a.work.exists(),'Fresh owned source-generation directory required');project=a.project_root.resolve(strict=True);ids=check_project(project);expected=locked(a.stage)
    original_input=project.parent/'RH080Study.v1/ablation/followup/independent-global-chord/inputs/w4.json';need(sha(original_input)==sha(PACKAGE/'locked/w4-input.json')==expected['input_sha256'],'Original mathematical input changed')
    flags=['-O']if sys.flags.optimize==1 else ['-OO']if sys.flags.optimize==2 else []
    a.work=a.work.absolute();a.work.mkdir(parents=True);original=a.work/'original-candidate';derived=a.work/'compact-candidate'
    commands=[[sys.executable,*flags,str(project/'dual/produce_fft_dag_certificate.py'),'--stages',str(a.stage),'--out',str(original),'--chunk-log',str(expected['chunk'].bit_length()-1),'--pairs-per-module',str(expected['pairs_per_module'])],[sys.executable,*flags,str(PACKAGE/'tools/derive_compact_candidate.py'),'--candidate',str(original),'--out',str(derived),'--project-root',str(project),'--input',str(PACKAGE/'locked/w4-input.json'),'--storage','hardlink']]
    publish(a.work/'PLAN.json',dict(status='PREPARED_UNTRUSTED_ORIGINAL_DATA_AND_SOURCE_ONLY_COMPACT_DERIVATION',stage=a.stage,commands=commands,source_pins=[dict(path=str(p),sha256=sha(p))for p in[Path(__file__),PACKAGE/'tools/derive_compact_candidate.py',PACKAGE/'tools/compact_contract.py',PACKAGE/'tools/generate_compact_final_v2.py',project/'dual/produce_fft_dag_certificate.py']]))
    started=time.monotonic();records=[]
    for i,command in enumerate(commands):
        tick=time.monotonic()
        with(a.work/f'step-{i}.stdout').open('xb')as out,(a.work/f'step-{i}.stderr').open('xb')as err:r=subprocess.run(command,stdout=out,stderr=err)
        row=dict(index=i,command=command,returncode=r.returncode,seconds=time.monotonic()-tick,stdout_sha256=sha(a.work/f'step-{i}.stdout'),stderr_sha256=sha(a.work/f'step-{i}.stderr'));publish(a.work/f'step-{i}.RECEIPT.json',row);records.append(row);need(r.returncode==0 and not(a.work/f'step-{i}.stderr').read_bytes(),'Source-only generation/derivation failed')
    state=validate_derived(derived,project);publish(a.work/'ORIGINAL_EXPECTED_INPUTS.json',dict(status='UNCHANGED_ORIGINAL_NUMERIC_EXPECTATIONS_NOT_DERIVED',original_plan_sha256=sha(original/'PLAN.json'),original_modules=state['original']['modules'],original_payloads=state['original']['payloads']))
    publish(a.work/'RESULT.json',dict(status='PASS_REGENERATED_ORIGINAL_AND_SOURCE_ONLY_COMPACT_CONTRACT_NOT_PROOF_NOT_PV',stage=a.stage,original_candidate=str(original),compact_candidate=str(derived),records=records,seconds=time.monotonic()-started,original_numeric_hashes_reproduced=True,original_expected_inputs_preserved=True,derived_plan_sha256=sha(derived/'PLAN.json'),no_Lean_proofs_compiled=True,new_heavy_N24_or681_replay_claimed=False,source_first_PV_complete=False));print('PASS CLEAN SOURCE ONLY COMPACT CONTRACT',a.stage,flush=True)
if __name__=='__main__':main()
