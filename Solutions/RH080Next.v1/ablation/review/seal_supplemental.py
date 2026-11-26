#!/usr/bin/env python3
"""Seal exact original locks, supplemental evidence and all16 mathematical readings.

This packages completed evidence; it does not write an IEANTN approval receipt or
reclassify original research outcomes. Source paths stay traceable to LOCK hashes.
"""
import argparse, json, shutil
from pathlib import Path
import run_review as common
import run_supplemental as worker
D = common.D
HERE = Path(__file__).resolve().parent


def copy_exact(source, target, digest=None):
    common.need(source.is_file() and not source.is_symlink(), 'Missing regular evidence file '+str(source))
    if digest is not None:
        common.need(common.sha(source) == digest, 'Evidence identity differs '+str(source))
    target.parent.mkdir(parents=True, exist_ok=True)
    common.need(not target.exists(), 'Fresh sealed path required')
    shutil.copyfile(source, target)
    common.need(common.sha(source) == common.sha(target), 'Evidence copy differs')


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args()
    common.need(not args.out.exists(), 'Fresh evidence destination required')
    recovery=common.load(D/'exposure-supplemental-recovery-v1/RESULT.json')
    accepted=common.load(worker.ROOT/'ACCEPTED.json')
    interpretation=common.load(worker.ROOT/'ALL16_MATHEMATICAL_INTERPRETATION_v2.json')
    common.need(len(recovery['rows']) == len(accepted['rows']) == 13 and len(interpretation['rows']) == 16,
                'Exact13/16 coverage required')
    common.need(interpretation['new_primary_successes'] == 0 and interpretation['external_model_inference_calls'] == 0,
                'Unexpected research or primary reclassification')
    args.out.mkdir(parents=True)
    payloads=[]
    for row in recovery['rows']:
        trial=row['trial']; root=Path(row['recovered_directory'])
        copy_exact(root/'LOCK.json', args.out/'locked_payloads'/trial/'LOCK.json', row['lock_sha256'])
        for artifact in row['artifacts']:
            copy_exact(root/artifact['path'], args.out/'locked_payloads'/trial/artifact['path'], artifact['sha256'])
        payloads.append(dict(trial=trial, lock_sha256=row['lock_sha256'],
                             files=[dict(path=a['path'],sha256=a['sha256']) for a in row['artifacts']],
                             primary_eligible=False))
    for row in accepted['rows']:
        run=Path(row['run']); target=args.out/'replay_evidence'/row['trial']
        for path in sorted((run/'submission').iterdir()):
            if path.is_file():
                copy_exact(path, target/'submission'/path.name)
        copy_exact(run/'result.json', target/'backend_result.json', row['backend_result_sha256'])
        copy_exact(run.with_name(run.name+'.INPUTS.json'),target/'INPUTS.json',row['inputs_sha256'])
    evidence={
        'EXACT_RECOVERY.json':D/'exposure-supplemental-recovery-v1/RESULT.json',
        'SELECTED_ALL13_RUNS.json':worker.ROOT/'SELECTED_ALL13_RUNS.json',
        'ACCEPTED.json':worker.ROOT/'ACCEPTED.json',
        'ACCEPTED.O.json':worker.ROOT/'ACCEPTED.O.json',
        'ACCEPTED.OO.json':worker.ROOT/'ACCEPTED.OO.json',
        'ACCEPTANCE_CONTROLS.json':worker.ROOT/'ACCEPTANCE_CONTROLS_v2/RESULT.json',
        'COORDINATOR_PREPARE_CONTROLS.json':worker.ROOT/'COORDINATOR_REPRO_CONTROLS_v1/RESULT.json',
        'ALL16_MATHEMATICAL_INTERPRETATION.json':worker.ROOT/'ALL16_MATHEMATICAL_INTERPRETATION_v2.json',
        'ORIGINAL_PRIMARY_SUMMARY.json':D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json',
        'ORIGINAL_COMMON_D_RUNTIME.json':worker.RUNTIME,
        'ORIGINAL13_PREFLIGHT.json':D/'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json',
        'ORIGINAL3_REVIEW_ACCEPTANCE.json':D/'exposure-independent-review-v1/ACCEPTED.json',
        'ORIGINAL_EXECUTED_COORDINATOR.py':worker.ROOT/'ALL13_BATCH_v1/coordinator.executed.py',
        'ORIGINAL_EXECUTED_V1_SCAFFOLD.py':D/'run_supplemental_v1.executed_scaffold.py',
    }
    for name,path in evidence.items():copy_exact(path,args.out/'evidence'/name)
    rows=[]
    for row in interpretation['rows']:
        extra=' '.join(row['extra_or_uninstantiated_interfaces'])
        limits=row['formal_tier']+'. '+row['endpoints_and_attainment']+' '+extra
        rows.append(dict(id=row['trial'],
            primary_status='Admissible; original status preserved' if row['primary_eligible'] else 'Censored by generated-output ceiling; primary inadmissible unchanged',
            verification_status='Primary exact-type/dependency proof review + independent mathematical reading' if row['primary_eligible'] else 'Supplemental exact-lock all-module compile/Std3 export + independent mathematical reading',
            mathematical_conclusion=row['mathematical_summary'],premise_limit=limits.strip()))
    common.save(args.out/'REPORT_EXPOSURE_ROWS.json',dict(rows=rows,
        interpretation_sha256=common.sha(evidence['ALL16_MATHEMATICAL_INTERPRETATION.json']),
        primary_admissible=3, primary_censored=13, new_primary_successes=0))
    runtime=common.load(worker.RUNTIME)
    deps=dict(runtime_sha256=worker.RUNTIME_SHA,
              same_original_runtime_for_all13=True, external_model_inference_calls=0,
              backend=dict(path=str(common.BACKEND),sha256=common.BACKEND_SHA),
              adapter=dict(path=str(common.S/'ablation/native_trial.py'),sha256=common.sha(common.S/'ablation/native_trial.py')),
              mounts=runtime['mounts'],lean_path=runtime['lean_path'],
              clean_replay_requires_mount_trees_and_original_executor=True,
              this_small_directory_is_not_the_complete_runtime_archive=True)
    common.save(args.out/'OFFLINE_DEPENDENCIES.json',deps)
    lines=['id,primary_status,verification_status,mathematical_conclusion,premise_limit']
    import csv,io
    stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    (args.out/'ALL16_RESULTS.csv').write_text(stream.getvalue())
    members=[dict(path=str(path.relative_to(args.out)),sha256=common.sha(path),bytes=path.stat().st_size)
             for path in sorted(args.out.rglob('*')) if path.is_file()]
    common.save(args.out/'MANIFEST.json',dict(status='SEALED_SUPPLEMENTAL_EVIDENCE_NOT_PRIMARY_RECLASSIFICATION',
                members=members,locked_rows=payloads,original_primary_admissible=3,
                original_primary_censored=13,new_primary_successes=0,
                source_modules=accepted['source_modules'],exported_constants=accepted['declarations'],
                theorem_kind_constants_including_generated_auxiliaries=accepted['theorems'],
                mathematical_strength_not_inferred_from_counts=True,
                seal_controller_sha256=common.sha(Path(__file__))))
    print('SEALED exact13lockedpayloads and all16interpretations:',args.out)


if __name__=='__main__':main()
