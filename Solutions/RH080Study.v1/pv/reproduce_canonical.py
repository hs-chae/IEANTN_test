#!/usr/bin/env python3
"""Focused canonical integration append against the immutable fresh PV bank.

This does not relabel future canonical faces as present in the earlier replay.
The 45-source cold C/mathematics phase must already be accepted and independently
read back; no predecessor application bank is admitted.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from reproduce_joint import need, sha, read, atomic, generic, memory_available, time_fields


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',required=True,type=Path)
    ap.add_argument('--context',required=True,type=Path)
    ap.add_argument('--accepted-run',required=True,type=Path)
    ap.add_argument('--run',type=Path)
    ap.add_argument('--check-only',action='store_true')
    a=ap.parse_args()
    repository=a.repository.resolve(strict=True); accepted=a.accepted_run.resolve(strict=True)
    compiler,libraries,dependencies=generic(read(a.context),repository)
    base=repository/'Solutions/RH080Study.v1'
    table=[('IEANTN.Vocabulary.CMSDual',repository/'IEANTN/Vocabulary/CMSDual.lean'),
           ('IEANTN.Nodes.CMSDualCertificate.v1.Conclusions',repository/'IEANTN/Nodes/CMSDualCertificate/v1/Conclusions.lean'),
           ('IEANTN.Nodes.CMSFunctionalObstruction.v1.Conclusions',repository/'IEANTN/Nodes/CMSFunctionalObstruction/v1/Conclusions.lean'),
           ('DualNetworkIntegration',base/'functional/DualNetworkIntegration.lean'),
           ('PVCanonicalAudit',base/'pv/lean/PVCanonicalAudit.lean'),
           ('PVBoundaryControls',base/'pv/lean/PVBoundaryControls.lean')]
    wrappers=[('CMSDualCertificate.v1',repository/'Solutions/CMSDualCertificate.v1/Solution.lean'),
              ('CMSFunctionalObstruction.v1',repository/'Solutions/CMSFunctionalObstruction.v1/Solution.lean')]
    need(read(accepted/'RESULT.json')['status']=='PASS_FRESH_COMPLETE_SOURCE_FIRST_DUAL_PROGRAM_AND_FULL_MATHEMATICAL_CONSUMER',
         'Accepted full source-only phase required')
    for _,p in table+wrappers:
        sha(p)
    if a.check_only:
        print(json.dumps(dict(status='PASS_CANONICAL_APPEND_PREFLIGHT_ONLY',fresh_bank=str(accepted),
                              source_files=len(table)+len(wrappers),previous_phase_not_retroactively_changed=True)))
        return
    need(a.run is not None and not a.run.exists(),'Fresh append --run required')
    run=a.run.resolve();run.mkdir(parents=True)
    source=run/'source';source.mkdir();objects=run/'objects';objects.mkdir();logs=run/'logs';logs.mkdir()
    started=time.monotonic()
    controller=Path(__file__);controller_sha=sha(controller)
    (run/'reproduce_canonical.executed.py').write_bytes(controller.read_bytes())
    provider=controller.with_name('reproduce_joint.py');provider_sha=sha(provider)
    (run/'reproduce_joint.provider.py').write_bytes(provider.read_bytes())
    verifier=controller.with_name('verify_joint.py');verifier_sha=sha(verifier)
    verify_command=[sys.executable,str(verifier),'--run',str(accepted),'--output',str(run/'COLD_READBACK.json')]
    verification=subprocess.run(verify_command,capture_output=True)
    (logs/'cold-readback.stdout').write_bytes(verification.stdout);(logs/'cold-readback.stderr').write_bytes(verification.stderr)
    need(verification.returncode==0,'Complete fresh source bank readback failed')
    cold_result_sha=sha(accepted/'RESULT.json')
    rows=[]
    for module,p in table:
        target=source/(module.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target)
        rows.append(dict(module=module,origin=str(p),source=str(target),sha256=sha(target),wrapper=False))
    for face,p in wrappers:
        target=source/'wrappers'/face/'Solution.lean';target.parent.mkdir(parents=True);shutil.copyfile(p,target)
        rows.append(dict(module='Solution',face=face,origin=str(p),source=str(target),sha256=sha(target),wrapper=True))
    atomic(run/'PLAN.json',dict(status='FROZEN_FOCUSED_APPEND_PLAN',previous_cold_run=str(accepted),
       previous_result_sha256=cold_result_sha,rows=rows,generic=dependencies,controller_sha256=controller_sha,
       provider_sha256=provider_sha,verifier_sha256=verifier_sha,
       phase='Focused canonical append; initial 45-module replay immutable',AS_cap_bytes=64*2**30))
    env=dict(os.environ,LEAN_PATH=str(objects)+':'+str(accepted/'objects')+':'+':'.join(libraries))
    builds=[]
    for row in rows:
        need(memory_available()>320*2**30,'Host reserve admission failed')
        module=row['module'];tag=row.get('face',module).replace('.','_')
        out=logs/(tag+'.stdout');err=logs/(tag+'.stderr');timing=logs/(tag+'.time')
        if row['wrapper']:
            bank=run/'wrapper-objects'/row['face'];bank.mkdir(parents=True)
            target=bank/'Solution.olean';root=Path(row['source']).parent
        else:
            target=objects/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);root=source
        command=['/usr/bin/time','-v','-o',str(timing),'prlimit','--as='+str(64*2**30),'--',
                 str(compiler),'-j2','-R',str(root),'-o',str(target),row['source']]
        began=time.monotonic()
        with out.open('wb') as o,err.open('wb') as e:
            completed=subprocess.run(command,cwd=root,env=env,stdout=o,stderr=e)
        item=dict(module=module,face=row.get('face'),command=command,returncode=completed.returncode,
                  seconds=time.monotonic()-began,source_sha256=sha(Path(row['source'])),
                  stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(timing),metrics=time_fields(timing))
        if completed.returncode!=0:
            atomic(run/'FAILED.json',dict(status='FAILED_CANONICAL_APPEND',builds=builds+[item]))
            raise ValueError('Canonical append failed: '+tag)
        item['object_sha256']=sha(target);builds.append(item)
    text=(logs/'PVCanonicalAudit.stdout').read_text()
    need('PV_CANONICAL_AUDIT_PASS roots=7 closed-source-paths=3 no-native no-sorry no-D-cap-shortcut' in text,
         'Canonical proof-value/axiom audit incomplete')
    need(text.count('PV_CANONICAL_AXIOMS ')==7 and text.count('PV_CANONICAL_SOURCE_CONSUMED ')==18,
         'Canonical actual audit population differs')
    need('sorryAx' not in text and 'ofReduceBool' not in text,'Forbidden canonical axiom')
    for row in rows:
        need(sha(Path(row['origin']))==row['sha256']==sha(Path(row['source'])),'Canonical source changed during append')
    need(sha(controller)==controller_sha and sha(provider)==provider_sha and sha(verifier)==verifier_sha,
         'Append controller/provider/validator changed')
    need(sha(accepted/'RESULT.json')==cold_result_sha,'Original accepted run changed')
    # Re-read every earlier accepted object/source after the focused append.
    final_readback=subprocess.run([sys.executable,str(verifier),'--run',str(accepted),'--output',str(run/'COLD_READBACK_FINAL.json')],capture_output=True)
    (logs/'cold-final.stdout').write_bytes(final_readback.stdout);(logs/'cold-final.stderr').write_bytes(final_readback.stderr)
    need(final_readback.returncode==0,'Original accepted bank changed during append')
    result=dict(status='PASS_CANONICAL_SOURCE_FIRST_INTEGRATION_APPEND',builds=builds,
       seconds=time.monotonic()-started,previous_cold_run=str(accepted),previous_result_sha256=cold_result_sha,
       plan_sha256=sha(run/'PLAN.json'),audit_sha256=sha(logs/'PVCanonicalAudit.stdout'),
       closed_canonical_roots=['RH080PV.Canonical.actual_ratio_floor','RH080PV.Canonical.actual_exclusion','RH080PV.Canonical.actual_network_result'],
       actual_source_syntax_main_and_numerical_execution_consumed=True,forbidden_native_axioms=False,
       canonical_mathematical_interface='Actual L1 Fourier dual witness and restricted ratio floor 100/123, excluding 4/5; not a prime-gap lower bound or unrestricted CMS optimizer.',
       limits='Focused append uses the accepted fresh 45-module application bank explicitly. Generic compiler/runtime/C ABI/OS/hardware contracts and conditional performed successful printf remain.',
       peak_individual_process_RSS_KiB=max(x['metrics'].get('peak_process_RSS_KiB',0) for x in builds),
       user_CPU_seconds=sum(x['metrics'].get('user_seconds',0) for x in builds),
       system_CPU_seconds=sum(x['metrics'].get('system_seconds',0) for x in builds),
       observed_SIGKILL_events=sum(x['returncode']==-9 for x in builds))
    atomic(run/'RESULT.json',result)
    print(json.dumps(dict(status=result['status'],source_files=len(rows),seconds=result['seconds'])))


if __name__=='__main__':
    main()
