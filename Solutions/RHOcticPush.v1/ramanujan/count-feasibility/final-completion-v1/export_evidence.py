#!/usr/bin/env python3
"""Read-only, hash-preserving export of already accepted finite-count evidence.

This is packaging, not mathematical acceptance. It deliberately never imports
the live validators, runs dependency probes, or reads numerical object banks.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
DATA = Path('/data/ivy-rh-octic-20261123/ramanujan')
EXPECTED = {
    'pure-count-recovery-v2/RESULT.json':
        '7af53640056a870b6cfb3e35b663b61b1e51916ce619e3a8c377eb7a9458d5f1',
    'cold-complement-v3/DATA_RESULT.json':
        '12c2e559748967c7a06ab001731a3f2fd140d9dc51e427f60014eab5fe819720',
    'cold-complement-v3/data-replay/RESULT.json':
        '384f222e4218a88c67a3eec973ad55cda91c9e31961c6b6941d474a4f89a6470',
    'cold-remaining-v3/RESULT.json':
        'e4c4c64102fcd6b598d0c1cb58f6abca38e9a67f0d42cf14c60faae1827577d0',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def export():
    rows = []

    def copy(relative, target, expected=None):
        source = DATA / relative
        need(source.is_file() and not source.is_symlink(), 'original regular evidence file')
        data = source.read_bytes()
        value = digest(data)
        need(expected is None or value == expected, 'unchanged accepted source receipt')
        destination = HERE / target
        destination.parent.mkdir(parents=True, exist_ok=True)
        need(not destination.exists() or destination.read_bytes() == data,
             'preserve previous evidence export bytes')
        destination.write_bytes(data)
        rows.append(dict(original=str(source), published=str(destination.relative_to(HERE)),
                         sha256=value, bytes=len(data)))

    for relative, expected in EXPECTED.items():
        copy(relative, 'receipts/' + relative, expected)
    measurements = [
        'pure-count-recovery-v2/RESUME_LAUNCHES/20261124T060015Z/resources.txt',
        'cold-complement-v3-launch/resources.txt',
        'cold-complement-v3-launch/LAUNCH.json',
        'cold-complement-v3-launch/V1_SAMPLER_LIMITATION.json',
        'cold-complement-v3-launch/sampled/monitor.executed.py',
        'cold-complement-v3-launch/sampled/METRICS.json',
        'cold-complement-v3-launch/MONITOR_V2_LAUNCH.json',
        'cold-complement-v3-launch/sampled-v2/METRICS.json',
        'cold-remaining-v3-launch/resources.txt',
        'cold-remaining-v3-launch/LAUNCH.json',
        'cold-remaining-v3-launch/sampled/METRICS.json',
        'cold-prepared-duplicate-cleanup/PREVIEW.json',
        'cold-prepared-duplicate-cleanup/RESULT.json',
        'cold-completed-controls-static-review-v1/FINAL_REVIEW.json',
        'passive-monitor-smoke-v1/RESULT.json',
        'passive-monitor-threaded-smoke-v2/RESULT.json',
        'passive-monitor-threaded-smoke-v2/threaded-root.executed.py',
    ]
    for relative in measurements:
        copy(relative, 'receipts/' + relative)
    report = read(DATA/'cold-remaining-v3/RESULT.json')
    by_name = {row['module']: row for row in report['records']}
    for name in ['SourceOutputAdapter', 'CountSourceFinal', 'CountSourceAudit']:
        row = by_name[name]
        attempt = Path(row['attempt'])
        need(attempt.is_relative_to(DATA/'cold-remaining-v3/attempts'),
             'actual accepted owned attempt')
        for filename, key in [('stdout', 'stdout_sha256'), ('stderr', 'stderr_sha256'),
                              ('resources', 'resources_sha256')]:
            copy(str((attempt/filename).relative_to(DATA)),
                 'compiled/' + name + '/' + filename, row[key])
        for filename in ['stdout', 'stderr']:
            copy(str((attempt/('deps.'+filename)).relative_to(DATA)),
                 'compiled/' + name + '/deps.' + filename,
                 row['dependency_probe'][filename+'_sha256'])

    dr = read(DATA/'cold-complement-v3/DATA_RESULT.json')
    semantic = digest(json.dumps(dr, sort_keys=True).encode())
    need(semantic == report['foundation']['cold_DATA_RESULT_sha256'],
         'exact historical semantic receipt serialization')
    metadata = dict(
        purpose='Hash-preserving read-only packaging; not a new verification receipt',
        actual305_status=report['status'],
        actual305_record_count=len(report['records']),
        raw_DATA_RESULT_sha256=EXPECTED['cold-complement-v3/DATA_RESULT.json'],
        sorted_semantic_DATA_RESULT_sha256=semantic,
        semantic_serialization_recipe=(
            'hashlib.sha256(json.dumps(json.loads(DATA_RESULT.read_text()), '
            'sort_keys=True).encode()).hexdigest(); Python default JSON separators; '
            'no trailing newline'),
        raw_remaining_RESULT_sha256=EXPECTED['cold-remaining-v3/RESULT.json'],
        original_no_historical_application_objects=report['no_historical_application_objects'],
        source_only_export_no_object_banks=True,
        actual30_controls='PENDING_EXCLUSIVE_VALIDATOR_WINDOW',
        evidence_rows=rows)
    target = HERE/'EVIDENCE_EXPORT.json'
    target.write_text(json.dumps(metadata, indent=2)+'\n')
    print(json.dumps(dict(files=len(rows), bytes=sum(row['bytes'] for row in rows),
                          export_sha256=digest(target.read_bytes()))))


if __name__ == '__main__':
    export()
