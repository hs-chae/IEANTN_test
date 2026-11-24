#!/usr/bin/env python3
"""Completed cold-source CLI controls; never manufacture a positive proof run.

Run only after the real695 and305 stages have completed. Negatives provide
read-only finite file views to the actual public CLIs. The original artifacts
remain intact. R's verifier also reruns its real dependency probes; their bytes
must remain unchanged across this entire control study.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import io
import json
import math
import os
import re
import runpy
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    return json.dumps(value, indent=2, allow_nan=False)+'\n'


def read(path):
    def pairs(items):
        value = {}
        for key, item in items:
            need(key not in value, 'duplicate control JSON key')
            value[key] = item
        return value
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(8 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def child(path):
    fixture = read(path)
    original_open = Path.open
    overrides = fixture['overrides']

    def finite_view(path, mode='r', buffering=-1, encoding=None, errors=None, newline=None):
        name = str(path.absolute())
        if name not in overrides:
            return original_open(path, mode, buffering, encoding, errors, newline)
        need(mode in ['r', 'rb'], 'fixture views are read-only')
        value = overrides[name]
        return io.BytesIO(value.encode()) if mode == 'rb' else io.StringIO(value)

    Path.open = finite_view
    script = HERE/fixture['script']
    sys.path.insert(0, str(HERE))
    sys.argv = [str(script), '--verify', '--out', fixture['run']]
    runpy.run_path(str(script), run_name='__main__')


def prepare(data, remaining, out):
    dr = read(data/'DATA_RESULT.json')
    rr = read(remaining/'RESULT.json')
    plan = read(remaining/'PLAN.json')
    need(dr['status'] == 'PASS_FRESH695_DATA_AND_GAPS_BYTE_IDENTICAL' and
         rr['status'] == 'PASS_NO_OLD_APPLICATION_CACHE_COUNT_AND_SOURCE_RUN' and
         len(dr['byte_identical_modules']) == 695 and len(rr['records']) == 305,
         'only real completed full695+305 results can be control inputs')
    need(plan['data_root'] == str(data), 'same actual prepared cold foundation')
    fixtures = []

    def add(name, script, run, gate, overrides):
        path = out/(name+'.fixture.json')
        value = dict(script=script, run=str(run), overrides=overrides)
        path.write_text(encode(value))
        fixtures.append(dict(name=name, script=script, run=str(run), fixture=str(path),
                             fixture_sha256=sha(path), expected_gate=gate))

    path = data/'PLAN.json'
    add('data_duplicate_JSON', 'data_stage.py', data, 'duplicate JSON key',
        {str(path): path.read_text().replace('{', '{"schema": "duplicate",', 1)})
    engine_path = data/'data-replay/RESULT.json'
    engine = read(engine_path)
    foreign = out/'foreign-byte-identical.olean'
    shutil.copyfile(Path(engine['records'][0]['object']), foreign)
    changed = copy.deepcopy(engine); changed['records'][0]['object'] = str(foreign)
    add('data_foreign_byte_identical_object', 'data_stage.py', data,
        'actual owned source/object/compiler command', {str(engine_path): encode(changed)})

    result_path = remaining/'RESULT.json'
    changed = copy.deepcopy(rr); changed['records'][0]['returncode'] = True
    add('remaining_boolean_compiler_success', 'remaining_stage.py', remaining,
        'exact successful actual compiler identity', {str(result_path): encode(changed)})
    usage = (Path(rr['records'][0]['attempt'])/'resources').read_text()
    match = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', usage)
    need(match is not None, 'actual first compiler GNU-time wall evidence')
    parts = match[1].split(':')
    need(len(parts) in [2, 3], 'canonical actual elapsed time')
    wall = sum(float(value)*60**index for index, value in enumerate(reversed(parts)))
    fabricated = wall+max(60, wall/2)+1
    need(math.isfinite(fabricated) and fabricated > wall+max(60, wall/2),
         'finite duration strictly beyond the original polling allowance')
    changed = copy.deepcopy(rr); changed['records'][0]['seconds'] = fabricated
    add('remaining_fictional_excessive_duration', 'remaining_stage.py', remaining,
        'observed completion duration agrees with GNU-time', {str(result_path): encode(changed)})
    changed = copy.deepcopy(rr)
    record = changed['records'][0]
    output = Path(record['attempt'])/'stdout'
    text = output.read_text()+'\nLean.ofReduceBool\n'
    record['stdout_sha256'] = hashlib.sha256(text.encode()).hexdigest()
    add('remaining_native_execution_leaf', 'remaining_stage.py', remaining,
        'no admitted or native execution proof leaf',
        {str(result_path): encode(changed), str(output): text})

    audit_index = next(i for i, row in enumerate(rr['records']) if row['module'] == 'CountSourceAudit')
    output = Path(rr['records'][audit_index]['attempt'])/'stdout'
    original = output.read_text()

    def audit_fixture(name, tag, mutation, gate):
        lines = original.splitlines()
        indexes = [i for i, line in enumerate(lines) if tag+' {' in line]
        need(indexes, 'actual full compiler audit marker')
        index = indexes[0]
        prefix, raw = lines[index].split(tag+' ', 1)
        payload = json.loads(raw)
        mutation(payload)
        lines[index] = prefix+tag+' '+json.dumps(payload, separators=(',', ':'))
        text = '\n'.join(lines)+'\n'
        changed = copy.deepcopy(rr)
        changed['records'][audit_index]['stdout_sha256'] = hashlib.sha256(text.encode()).hexdigest()
        add(name, 'remaining_stage.py', remaining, gate,
            {str(result_path): encode(changed), str(output): text})

    audit_fixture('remaining_omitted_VALUE_endpoint', 'COLD_SOURCE_VALUE_PATH',
        lambda value: value['required'].pop(),
        'all exact twelve source/count proof VALUE endpoints, never a selected subset')
    audit_fixture('remaining_duplicate_axiom_metadata', 'COLD_SOURCE_THEOREM',
        lambda value: value.update(axioms=['propext', 'propext']),
        'strict unique actual source/consumer theorem axiom rows')
    changed = copy.deepcopy(rr)
    changed['records'][0]['dependency_probe']['stdout_sha256'] = hashlib.sha256(b'').hexdigest()
    add('remaining_omitted_recorded_dependency', 'remaining_stage.py', remaining,
        'fresh actual dependency readback', {str(result_path): encode(changed)})
    return fixtures, rr


def main_run(data, remaining, out):
    data, remaining, out = data.resolve(), remaining.resolve(), out.resolve()
    need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(data) and
         not out.is_relative_to(remaining), 'fresh independent control output')
    out.mkdir()
    (out/'test.executed.py').write_bytes(Path(__file__).read_bytes())
    fixtures, result = prepare(data, remaining, out)
    protected = [data/'DATA_RESULT.json', data/'PLAN.json', data/'data-replay/RESULT.json',
                 remaining/'RESULT.json', remaining/'PLAN.json']
    for row in result['records']:
        protected += [Path(row['attempt'])/name for name in ['stdout', 'stderr', 'deps.stdout', 'deps.stderr']]
    before = {str(path): sha(path) for path in protected}
    records = []
    try:
        for mode_index, flags in enumerate([[], ['-O'], ['-OO']]):
            tests = [dict(name='data_actual_positive', script='data_stage.py', run=str(data), fixture=None),
                     dict(name='remaining_actual_positive', script='remaining_stage.py',
                          run=str(remaining), fixture=None)]+fixtures
            for test in tests:
                label = str(mode_index)+'-'+test['name']
                command = [sys.executable, *flags]
                command += [str(HERE/test['script']), '--verify', '--out', test['run']] \
                    if test['fixture'] is None else [str(Path(__file__).resolve()), '--child', test['fixture']]
                start = time.monotonic()
                cp = subprocess.run(command, capture_output=True, text=True,
                    env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
                for suffix, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
                    (out/(label+'.'+suffix)).write_text(text)
                positive = test['fixture'] is None
                passed = cp.returncode == 0 and 'PASS_' in cp.stdout if positive else \
                    cp.returncode != 0 and test['expected_gate'] in cp.stderr
                row = dict(name=test['name'], optimization=flags, command=command,
                    returncode=cp.returncode, seconds=time.monotonic()-start, passed=passed,
                    expected_gate=test.get('expected_gate'), stdout_sha256=sha(out/(label+'.stdout')),
                    stderr_sha256=sha(out/(label+'.stderr')))
                if test['fixture']:
                    row['fixture_sha256'] = test['fixture_sha256']
                records.append(row)
                (out/'PROGRESS.json').write_text(encode(dict(completed=len(records), records=records)))
                need(passed, 'completed full-source actual CLI control failed:'+label)
    finally:
        after = {str(path): sha(path) for path in protected}
        changed = [dict(path=path, before_sha256=before[path], after_sha256=after[path])
                   for path in before if before[path] != after[path]]
        preservation = dict(original_receipt_log_bytes_unchanged=not changed,
            checked_original_files=len(before), changed=changed, completed_decisions=len(records))
        temporary = out/'.PRESERVATION.json.pending'
        temporary.write_text(encode(preservation)); os.replace(temporary, out/'PRESERVATION.json')
        need(not changed, 'all original completed receipts/log bytes unchanged after real dependency re-probes')
    report = dict(status='PASS_COMPLETED_FULL_COLD695_AND305_PUBLIC_CLI_CONTROLS',
        test_sha256=sha(__file__), data_result_sha256=sha(data/'DATA_RESULT.json'),
        remaining_result_sha256=sha(remaining/'RESULT.json'),
        data_controller_sha256=sha(HERE/'data_stage.py'),
        remaining_controller_sha256=sha(HERE/'remaining_stage.py'),
        decisions=len(records), records=records, original_receipt_log_bytes_unchanged=True,
        scope='Six real public-CLI positive readbacks and24 read-only metadata-view negative '
              'CLI cases across normal/-O/-OO. Existing verifier reruns real dependency probes. '
              'These controls are not new mathematical proof executions.')
    temporary = out/'.RESULT.json.pending'; temporary.write_text(encode(report))
    os.replace(temporary, out/'RESULT.json')
    print(report['status'], len(records))


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--data', type=Path)
    parser.add_argument('--remaining', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--child', type=Path)
    args = parser.parse_args()
    if args.child:
        need(args.data is None and args.remaining is None and args.out is None, 'one child fixture')
        child(args.child)
    else:
        need(args.data is not None and args.remaining is not None and args.out is not None,
             'explicit actual completed stages and control output')
        main_run(args.data, args.remaining, args.out)


if __name__ == '__main__':
    main()
