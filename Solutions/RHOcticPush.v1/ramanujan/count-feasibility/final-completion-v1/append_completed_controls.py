#!/usr/bin/env python3
"""Export the actual completed30 study without re-running any live validator.

This packages existing CLI evidence. The mathematical results remain justified
by their original Lean compilation and source/count acceptance pipelines.
"""
from pathlib import Path
import hashlib
import json
import math
import os
import re

HERE = Path(__file__).resolve().parent
COUNT = HERE.parent
ROOT = COUNT.parents[3]
DATA = Path('/data/ivy-rh-octic-20261123/ramanujan')
CONTROLS = DATA/'cold-completed-controls-v1'
LAUNCH = DATA/'cold-completed-controls-v1-launch'
TEST_SHA = 'a351472d16a111485daf67b182744ac8bed85eff1d2057146b676f064ebc9ba9'
PRIOR_SHA = '0515ce85b0958b4b33e286a88b54d43ab0ec47706fac1dcf0a93cbb061c19207'
OVERLAY = 'Solutions/RHOcticPush.v1/integration/continuation/CURRENT_DOCUMENTATION_OVERLAY.json'
OVERLAY_SHA = '09d1086495ba23f5168f4d1f4f7fc01c4e2daa01c2f6bb6eaa01220a0e5e620b'
README = 'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/final-completion-v1/README.md'
ARCHIVED_README = ('Solutions/RHOcticPush.v1/history/entrypoints-before-completion-update-20261124/'
                  'ramanujan/count-feasibility/final-completion-v1/README.md')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate receipt JSON key')
            result[key] = value
        return result
    def finite(value):
        number = float(value)
        need(math.isfinite(number), 'finite receipt number')
        return number
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
        parse_float=finite,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite receipt')))


def write(path, value):
    data = (json.dumps(value, indent=2, allow_nan=False)+'\n').encode()
    need(not path.exists() or path.read_bytes() == data, 'preserve earlier completed export')
    temporary = path.with_name('.'+path.name+'.pending')
    need(not temporary.exists(), 'fresh atomic export temporary')
    temporary.write_bytes(data)
    os.replace(temporary, path)


def main():
    prior = HERE/'PUBLIC_ALLOWLIST_PENDING30.json'
    need(sha(prior) == PRIOR_SHA, 'unchanged dated checkpoint7 manifest')
    need(sha(ROOT/OVERLAY) == OVERLAY_SHA, 'exact published chronological documentation overlay')
    replacements = [row for row in read(ROOT/OVERLAY)['replacements'] if row['path'] == README]
    need(len(replacements) == 1, 'only the exact dated README replacement')
    replacement = replacements[0]
    need(replacement['archived_path'] == ARCHIVED_README and
         replacement['old_sha256'] ==
         'c5d42f33e18917879acf2eb5b9ab67f4eccd818b76edf7d46770f5e9d9859618' and
         replacement['new_sha256'] ==
         '07126f439f7e9d0c5f624ef71fdd12d741d5f0ee3a1230b0ef0e0d2566eea5ef',
         'explicit original/current documentation identities, not proof-source substitution')
    for row in read(prior)['rows']:
        path = ROOT/row['path']
        if row['path'] == README:
            need(path.is_file() and not path.is_symlink() and
                 path.stat().st_size == replacement['new_bytes'] and
                 sha(path) == replacement['new_sha256'] and
                 row['sha256'] == replacement['old_sha256'] and
                 row['bytes'] == replacement['old_bytes'], 'exact current README overlay only')
            path = ROOT/ARCHIVED_README
        need(path.is_file() and not path.is_symlink() and
             path.resolve().is_relative_to(ROOT) and path.stat().st_size == row['bytes'] and
             sha(path) == row['sha256'],
             'every frozen checkpoint7 row remains unchanged')
    report = read(CONTROLS/'RESULT.json')
    need(report['status'] == 'PASS_COMPLETED_FULL_COLD695_AND305_PUBLIC_CLI_CONTROLS' and
         type(report['decisions']) is int and report['decisions'] == 30,
         'actual completed30 result, never partial progress')
    need(report['test_sha256'] == TEST_SHA == sha(COUNT/'cold-foundation/test_completed.py') ==
         sha(CONTROLS/'test.executed.py') == sha(LAUNCH/'test.executed.py'),
         'unchanged reviewed actually executed control source')
    need(report['data_result_sha256'] ==
         '12c2e559748967c7a06ab001731a3f2fd140d9dc51e427f60014eab5fe819720' ==
         sha(DATA/'cold-complement-v3/DATA_RESULT.json') and
         report['remaining_result_sha256'] ==
         'e4c4c64102fcd6b598d0c1cb58f6abca38e9a67f0d42cf14c60faae1827577d0' ==
         sha(DATA/'cold-remaining-v3/RESULT.json'), 'unchanged actual mathematical receipts')
    need(report['data_controller_sha256'] ==
         'd86e7a41775bc03d50350c4b00ad768636ba0b030a58abc9fb831a7488644980' and
         report['remaining_controller_sha256'] ==
         '27f8f3b4ffb0443e3880cc2bc928110c1ecd87143e8e5ff0f10cc26453bb729c',
         'original mathematical readers')
    preservation = read(CONTROLS/'PRESERVATION.json')
    need(preservation['original_receipt_log_bytes_unchanged'] is True and
         preservation['changed'] == [] and
         type(preservation['checked_original_files']) is int and
         preservation['checked_original_files'] == 1225 and
         type(preservation['completed_decisions']) is int and
         preservation['completed_decisions'] == 30 and
         report['original_receipt_log_bytes_unchanged'] is True,
         'actual original1225receipt/log bytes preserved through all30')
    launch = read(LAUNCH/'LAUNCH.json')
    proc = Path('/proc')/str(launch['PID'])/'stat'
    if proc.exists():
        text = proc.read_text()
        fields = text[text.rfind(')')+2:].split()
        need(fields[19] != launch['start_ticks'] or fields[0] == 'Z',
             'original GNU controller no longer executing before export')
    usage = (LAUNCH/'resources.txt').read_text()
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', usage)
    peak = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
    need(wall is not None and peak is not None and
         re.search(r'Exit status:\s*0\s*$', usage), 'full external GNU-time exit0/wall/RSS')

    names = ['data_actual_positive', 'remaining_actual_positive', 'data_duplicate_JSON',
             'data_foreign_byte_identical_object', 'remaining_boolean_compiler_success',
             'remaining_fictional_excessive_duration', 'remaining_native_execution_leaf',
             'remaining_omitted_VALUE_endpoint', 'remaining_duplicate_axiom_metadata',
             'remaining_omitted_recorded_dependency']
    need(len(report['records']) == 30, 'exact actual30 rows')
    exported = []

    def copy(path, destination):
        need(path.is_file() and not path.is_symlink(), 'original regular experiment evidence')
        target = HERE/'completed30'/destination
        target.parent.mkdir(parents=True, exist_ok=True)
        data = path.read_bytes()
        need(not target.exists() or target.read_bytes() == data, 'immutable exported evidence')
        target.write_bytes(data)
        exported.append(dict(original=str(path), path=str(target.relative_to(ROOT)),
                             sha256=sha(path), bytes=len(data)))

    for index, row in enumerate(report['records']):
        mode, offset = divmod(index, 10)
        flags = [[], ['-O'], ['-OO']][mode]
        positive = offset < 2
        need(row['name'] == names[offset] and row['optimization'] == flags and
             row['passed'] is True and type(row['returncode']) is int and
             ((row['returncode'] == 0) if positive else (row['returncode'] != 0)),
             'exact six real positive and24 negative actual mode identities')
        label = str(mode)+'-'+row['name']
        stdout, stderr = CONTROLS/(label+'.stdout'), CONTROLS/(label+'.stderr')
        need(sha(stdout) == row['stdout_sha256'] and sha(stderr) == row['stderr_sha256'],
             'actual original60CLI log hashes')
        if positive:
            need('PASS_' in stdout.read_text() and stderr.read_bytes() == b'',
                 'real successful public reader stdout, no stderr')
            script = 'data_stage.py' if offset == 0 else 'remaining_stage.py'
            base = DATA/('cold-complement-v3' if offset == 0 else 'cold-remaining-v3')
            suffix = [str(COUNT/'cold-foundation'/script), '--verify', '--out', str(base)]
        else:
            fixture = CONTROLS/(row['name']+'.fixture.json')
            need(sha(fixture) == row['fixture_sha256'] and
                 type(row['expected_gate']) is str and row['expected_gate'] and
                 row['expected_gate'] in stderr.read_text(),
                 'specific intended negative gate and original fixture identity')
            suffix = [str(COUNT/'cold-foundation/test_completed.py'), '--child', str(fixture)]
        interpreter = launch['command'][launch['command'].index('--')+1]
        need(row['command'] == [interpreter, *flags, *suffix],
             'actual original CLI argv, no fixture presented as real positive')
        copy(stdout, 'logs/'+label+'.stdout')
        copy(stderr, 'logs/'+label+'.stderr')
    for name in ['RESULT.json', 'PRESERVATION.json', 'PROGRESS.json', 'test.executed.py']:
        copy(CONTROLS/name, name)
    for name in ['LAUNCH.json', 'resources.txt', 'stdout', 'stderr', 'test.executed.py']:
        copy(LAUNCH/name, 'launch/'+name)
    value = dict(status='READ_ONLY_EXPORT_OF_ACTUAL_COMPLETED30_CLI_STUDY',
        checkpoint7_documentation_resolution=dict(overlay_sha256=OVERLAY_SHA,
            original_dated_README=ARCHIVED_README,
            current_logical_README_sha256=replacement['new_sha256'],
            all_other58_checkpoint_rows_direct_and_unchanged=True),
        actual_RESULT_sha256=sha(CONTROLS/'RESULT.json'),
        raw_DATA_RESULT_sha256=report['data_result_sha256'],
        raw_remaining_RESULT_sha256=report['remaining_result_sha256'],
        preservation_sha256=sha(CONTROLS/'PRESERVATION.json'),
        six_real_positive_CLI_readbacks=6, read_only_metadata_view_negative_CLI_cases=24,
        checked_original_receipt_log_files=1225,
        GNU_full_wall=wall[1], GNU_maximum_child_RSS_bytes=int(peak[1])*1024,
        owned_control_directory_allocated_bytes=sum(path.stat().st_blocks*512
            for path in CONTROLS.rglob('*') if path.is_file() and not path.is_symlink()),
        fixtures_retained_on_server=True,
        mathematical_proof_execution_claim=False,
        scope='Actual mathematical proofs were accepted earlier. These30CLIs test their engineering '
              'readers in normal/-O/-OO modes; negative fixtures do not execute mathematical proofs. '
              'Fixture source and deterministic construction are preserved; only concise evidence is exported.',
        evidence=exported)
    write(HERE/'ACTUAL30_EXPORT.json', value)
    print(value['status'], value['actual_RESULT_sha256'], len(exported))


if __name__ == '__main__':
    main()
