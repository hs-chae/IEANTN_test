#!/usr/bin/env python3
"""Recreate concise census/resources from published raw receipts, without banks.

This packages previously accepted evidence; it is not a substitute for Lean or
the original numerical/source acceptance pipeline.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ORIGINAL = Path('/data/ivy-rh-octic-20261123/ramanujan')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(relative):
    return HERE/'receipts'/relative


def gnu(relative):
    path = receipt(relative)
    text = path.read_text()
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', text)
    rss = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', text)
    exit_code = re.search(r'Exit status:\s*(\d+)', text)
    need(wall is not None and rss is not None and exit_code is not None, 'actual GNU-time fields')
    return dict(original=str(ORIGINAL/relative), sha256=sha(path), wall_display=wall[1],
        wall_seconds=sum(float(value)*60**index
                         for index, value in enumerate(reversed(wall[1].split(':')))),
        maximum_child_RSS_bytes=int(rss[1])*1024, exit_code=int(exit_code[1]),
        scope='GNU-time around original full stage controller, including its final acceptance readback; '
              'max-child is not simultaneous aggregate RAM')


def census(warm, remaining, engine):
    prefix = 'RamanujanPV.HighTransitionCount.'
    leaves = {}
    for row in warm['records']:
        if row['module'].startswith(prefix+'Check'):
            proof = row['proof']
            need(len(proof['axioms']) == 1 and next(iter(proof['axioms'].values())) == [],
                 'exact empty current-campaign arithmetic receipt')
            leaves[row['module']] = dict(module=row['module'], axioms=proof['axioms'],
                source_sha256=proof['source_sha256'], object_sha256=proof['object_sha256'],
                origin='current-campaign2469')
    for row in remaining['records']:
        if row['module'].startswith(prefix+'Check'):
            need(row['module'] not in leaves and len(row['axioms']) == 1 and
                 next(iter(row['axioms'].values())) == [], 'disjoint empty fresh299 receipt')
            leaves[row['module']] = dict(module=row['module'], axioms=row['axioms'],
                source_sha256=row['source_sha256'], object_sha256=row['object_sha256'],
                origin='fresh299')
    need(set(leaves) == {prefix+'Check'+format(index, '04d') for index in range(2768)},
         'exact fixed all2768 arithmetic source identities')
    text = (HERE/'compiled/CountSourceAudit/stdout').read_text()
    rows = [json.loads(line.split('COLD_SOURCE_THEOREM ', 1)[1])
            for line in text.splitlines() if line.startswith('COLD_SOURCE_THEOREM ')]
    payloads = [json.loads(line.split('COLD_SOURCE_VALUE_PATH ', 1)[1])
                for line in text.splitlines() if line.startswith('COLD_SOURCE_VALUE_PATH ')]
    need(len(rows) == 13 and len(payloads) == 1 and
         all(set(row['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'} for row in rows),
         'actual final source audit records')
    return dict(status='READ_ONLY_EXTRACTION_OF_ACCEPTED_PROOF_RECEIPTS',
        all2768_arithmetic_axioms_empty=True,
        arithmetic_records=sorted(leaves.values(), key=lambda row: row['module']),
        actual13_theorem_rows=rows, actual_value_payload=payloads[0],
        cold_engine_axioms=engine['axioms'],
        native_execution_axioms_in_selected_final_count_source_roots=False,
        scope='Extraction of previously accepted actual compile/audit records; no new compiler/validator '
              'execution. Syntax/model adequacy and physical compiled-run interpretation are separate '
              'documented trust boundaries.')


def resources(warm, remaining, engine):
    cold_samples = read(receipt('cold-complement-v3-launch/sampled-v2/METRICS.json'))
    remaining_samples = read(receipt('cold-remaining-v3-launch/sampled/METRICS.json'))
    return dict(status='READ_ONLY_RESOURCE_EXTRACTION_ACTUAL_ACCEPTED_RUNS',
        units='All numeric memory/disk fields bytes; GiB=2^30 bytes; GNU-time kbytes converted by1024.',
        warm_resume=dict(
            GNU_time=gnu('pure-count-recovery-v2/RESUME_LAUNCHES/20261124T060015Z/resources.txt'),
            internal_pre_final_validation_seconds=warm['seconds_this_attempt'],
            internal_current_attempt_sampled_peaks=warm['resource_peaks_this_attempt'],
            whole_campaign_resource_peaks=warm['whole_campaign_evidence']['whole_campaign_resource_peaks'],
            owned_scratch_final_bytes=warm['owned_scratch_final_bytes'],
            confirmed_kernel_OOM_kills=warm['whole_campaign_evidence']['confirmed_kernel_OOM_kills'],
            scope='Current resumed controller is a subset of whole campaign. Narrow internal seconds exclude '
                  'initial/final complete reader portions; GNU full wall is external3:41:35. Historical '
                  'intentionalSIGUSR1 usage drains are preserved.'),
        cold695=dict(GNU_time=gnu('cold-complement-v3-launch/resources.txt'),
            declared_source_targets=696, numerical_data_and_gap_modules=695,
            actual_compiler_records_including_generated_audit=697,
            internal_engine_seconds=engine['seconds'],
            actual_peak_worker_rss_bytes=engine['actual_peak_worker_rss_bytes'],
            actual_replay_disk_bytes=engine['actual_replay_disk_bytes'],
            owned_OOM_events=engine['oom_events'], passive_metrics=cold_samples,
            scope='V1main-thread-only sampler missed threaded engine descendants; preserved incomplete. '
                  'V2ALL_THREAD_CHILDREN starts10:23:47 after first raw dispatch and covers last3072.067s; '
                  'no whole interval exact aggregate claim. Actual timestamp spacing includes proc scans; '
                  'not exact1Hz.'),
        cold_remaining305=dict(GNU_time=gnu('cold-remaining-v3-launch/resources.txt'),
            internal_pre_final_validation_seconds=remaining['seconds'],
            internal_controller_sampled_peaks=remaining['resource_peaks'],
            whole_outer_stage_passive_metrics=remaining_samples,
            scope='Independent passive monitor covers4100.711s including final validator and samples broader '
                  'wrapper forest. Its RSS/PSS maxima differ from internal earlier controller samples; neither '
                  'is an exact simultaneous whole-run peak.'),
        cleanup=dict(retained_accepted_proofs_and_original_sources=True,
            deleted_only_verified_regenerable_unused_duplicate_sources_allocated_bytes=16907546624,
            result_path=str(ORIGINAL/'cold-prepared-duplicate-cleanup/RESULT.json')),
        remaining_limits='Restricted-C execution-model adequacy, compiler/runtime, ABI/stdio/OS/hardware '
                         'contracts are separate from arithmetic kernel proofs and syntactic correspondence. '
                         'Resource observations are not mathematical acceptance.')


def main():
    exported = read(HERE/'EVIDENCE_EXPORT.json')
    for row in exported['evidence_rows']:
        path = HERE/row['published']
        need(path.is_file() and sha(path) == row['sha256'] and path.stat().st_size == row['bytes'],
             'unchanged published raw evidence')
    warm = read(receipt('pure-count-recovery-v2/RESULT.json'))
    remaining = read(receipt('cold-remaining-v3/RESULT.json'))
    engine = read(receipt('cold-complement-v3/data-replay/RESULT.json'))
    for name, value in [('PROOF_CENSUS.json', census(warm, remaining, engine)),
                        ('RESOURCE_SUMMARY.json', resources(warm, remaining, engine))]:
        data = (json.dumps(value, indent=2)+'\n').encode()
        destination = HERE/name
        need(not destination.exists() or destination.read_bytes() == data,
             'exact deterministic regeneration of '+name)
        destination.write_bytes(data)
        print(name, hashlib.sha256(data).hexdigest())


if __name__ == '__main__':
    main()
