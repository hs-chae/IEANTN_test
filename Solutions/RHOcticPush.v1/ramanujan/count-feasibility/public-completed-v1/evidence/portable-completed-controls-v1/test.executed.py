#!/usr/bin/env python3
"""Actual public CLI positives and read-only mutation-view controls.

Negatives inject finite file-byte fixtures into Path.open in a fresh CLI process.
They never edit the accepted experiment or claim to be another executed proof.
This distinction is included in the atomic control receipt.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import io
import json
import os
import runpy
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encode(value):
    return json.dumps(value, indent=2, allow_nan=False)+'\n'


def load(path):
    return json.loads(Path(path).read_text())


def child(fixture):
    fixture = load(fixture)
    overrides = fixture['overrides']
    original = Path.open

    def fixture_open(path, mode='r', buffering=-1, encoding=None, errors=None, newline=None):
        key = str(path.absolute())
        if key not in overrides:
            return original(path, mode, buffering, encoding, errors, newline)
        need(mode in ['r', 'rb'], 'mutation fixtures are strictly read-only')
        value = overrides[key]
        return io.BytesIO(value.encode()) if mode == 'rb' else io.StringIO(value)

    Path.open = fixture_open
    sys.argv = [str(HERE/'reproduce.py'), '--check', fixture['actual_completed_run']]
    if fixture.get('extra_arguments'):
        sys.argv += fixture['extra_arguments']
    # Execute the same public argument parser, dispatch and full reader as users.
    # No acceptance predicate or source implementation is replaced.
    runpy.run_path(str(HERE/'reproduce.py'), run_name='__main__')


def fixtures(actual, output):
    plan_path, result_path = actual/'PLAN.json', actual/'RESULT.json'
    engine_result_path = actual/'replay/RESULT.json'
    plan, result, engine = load(plan_path), load(result_path), load(engine_result_path)
    need(plan['smoke'] is True and result['fixed_high_output_proved'] is False,
         'this fixture universe is the actual N1000 source-clean workflow control')
    rows = []

    def case(name, gate, mapping=None, extra=None):
        path = output/(name+'.fixture.json')
        payload = dict(actual_completed_run=str(actual), overrides=mapping or {},
                       extra_arguments=extra or [])
        path.write_text(encode(payload))
        rows.append(dict(name=name, expected_gate=gate, fixture=str(path),
                         fixture_sha256=sha(path)))

    def mutated(path, value):
        return {str(path): encode(value)}

    q = copy.deepcopy(plan); q['jobs'] = True
    case('boolean_worker_count', 'strict bounded portable worker/CPU metadata', mutated(plan_path, q))
    q = copy.deepcopy(plan); q['smoke'] = 1.0
    case('float_smoke_scope', 'strict smoke/full distinction', mutated(plan_path, q))
    q = copy.deepcopy(plan); q['sources'].pop()
    case('omitted_source', 'complete source capture without replacement or omitted numerical parts',
         mutated(plan_path, q))
    raw = plan_path.read_text()
    case('duplicate_json_key', 'duplicate JSON key', {str(plan_path): raw.replace('{', '{"jobs": 1,', 1)})
    q = copy.deepcopy(plan); q['jobs'] = 1e309
    case('nonfinite_json_number', 'nonfinite JSON number',
         {str(plan_path): json.dumps(q, allow_nan=True).replace('Infinity', '1e1000')})
    case('conflicting_public_cli_route', 'readback route arguments', extra=['--smoke'])
    path = actual/'compile_all.json'; q = load(path); q['seconds'] = 1
    case('fictional_one_second_stage', 'observed completion duration agrees with GNU-time',
         mutated(path, q))
    path = actual/'regenerate.json'; q = load(path); q['returncode'] = True
    case('boolean_stage_success', 'exact successful actual top-level stage command:regenerate',
         mutated(path, q))
    q = copy.deepcopy(plan); q['command'][q['command'].index('--jobs')+1] = '2'
    case('different_engine_command', 'canonical whole-source execution command', mutated(plan_path, q))
    q = copy.deepcopy(engine); q['records'][0]['command'][1] = '-j2'
    case('different_compiler_command', 'exact actual source/compiler/object command',
         mutated(engine_result_path, q))
    foreign = output/'foreign-byte-identical.olean'
    foreign.write_bytes(Path(engine['records'][0]['object']).read_bytes())
    q = copy.deepcopy(engine); q['records'][0]['object'] = str(foreign)
    case('foreign_byte_identical_object', 'owned regular actual replay file',
         mutated(engine_result_path, q))
    q = copy.deepcopy(engine); q['records'][0]['seconds'] = -1
    case('negative_compiler_duration', 'finite actual GNU-time wall evidence',
         mutated(engine_result_path, q))
    q = copy.deepcopy(engine); q['records'][0]['source_unchanged_during_compile'] = 1
    case('integer_unchanged_source_flag', 'actual source success and exact address-space cap',
         mutated(engine_result_path, q))
    modules = load(actual/'replay/PLAN.json')['modules']
    names = {row['module'] for row in modules}
    chosen = next(row for row in modules if any(x in names for x in row['imports']))
    directory = actual/'dependencies'/chosen['module']
    path = directory/'stdout'; probe_path = directory/'PROBE.json'
    probe = load(probe_path); probe['stdout_sha256'] = hashlib.sha256(b'').hexdigest()
    case('empty_dependency_probe', 'nonempty dependency paths',
         {str(path): '', str(probe_path): encode(probe)})
    direct = next(name for name in chosen['imports'] if name in names)
    omit = str(actual/'replay/lean'/Path(*direct.split('.')).with_suffix('.olean'))
    lines = path.read_text().splitlines()
    need(omit in lines, 'actual direct dependency exists in real positive output')
    changed = '\n'.join(line for line in lines if line != omit)+'\n'
    need(changed.strip(), 'nonempty direct-import omission control')
    probe = load(probe_path); probe['stdout_sha256'] = hashlib.sha256(changed.encode()).hexdigest()
    case('omitted_direct_application_import', 'every actual declared direct application import',
         {str(path): changed, str(probe_path): encode(probe)})
    q = copy.deepcopy(result); q['fixed_high_output_proved'] = True
    case('smoke_relabelled_full_output', 'complete exact independent portable result readback',
         mutated(result_path, q))
    return rows


def run(actual, output):
    actual, output = actual.resolve(), output.resolve()
    need(not output.exists() and output.parent.is_dir(), 'fresh owned control output')
    output.mkdir()
    script = output/'test.executed.py'; script.write_bytes(Path(__file__).read_bytes())
    original_result = sha(actual/'RESULT.json')
    cases = fixtures(actual, output)
    records = []
    modes = [[], ['-O'], ['-OO']]
    for index, mode in enumerate(modes):
        tests = [dict(name='actual_positive', expected_gate=None, fixture=None)]+cases
        for test in tests:
            label = str(index)+'-'+test['name']
            command = [sys.executable, *mode]
            command += [str(HERE/'reproduce.py'), '--check', str(actual)] if test['fixture'] is None \
                else [str(Path(__file__).resolve()), '--child', test['fixture']]
            start = time.monotonic()
            cp = subprocess.run(command, capture_output=True, text=True,
                                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
            for suffix, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
                (output/(label+'.'+suffix)).write_text(text)
            positive = test['fixture'] is None
            passed = cp.returncode == 0 and 'PASS_SMOKE_1000' in cp.stdout if positive else \
                cp.returncode != 0 and test['expected_gate'] in cp.stderr
            row = dict(name=test['name'], optimization=mode, command=command,
                returncode=cp.returncode, seconds=time.monotonic()-start,
                expected_gate=test['expected_gate'], passed=passed,
                stdout_sha256=sha(output/(label+'.stdout')),
                stderr_sha256=sha(output/(label+'.stderr')))
            if test['fixture']:
                row['fixture_sha256'] = test['fixture_sha256']
            records.append(row)
            (output/'PROGRESS.json').write_text(encode(dict(complete=len(records), records=records)))
            need(passed, 'actual CLI control failed:'+label)
    need(sha(actual/'RESULT.json') == original_result, 'accepted result untouched')
    result = dict(status='PASS_COMPLETED_PORTABLE_PUBLIC_CLI_CONTROLS',
        actual_completed_result=str(actual/'RESULT.json'), actual_result_sha256=original_result,
        checker_sha256=sha(HERE/'reproduce.py'), reader_sha256=sha(HERE/'readback.py'),
        test_sha256=sha(__file__), decisions=len(records), records=records,
        scope='Three real positive public-CLI readbacks; negative public-CLI runs use labeled '
              'read-only file-byte views. No original artifact is edited; fixtures are not executed proofs.',
        no_new_numerical_or_high_output_claim=True)
    temporary = output/'.RESULT.json.pending'
    temporary.write_text(encode(result)); os.replace(temporary, output/'RESULT.json')
    print(result['status'], len(records))


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--actual', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--child', type=Path)
    args = parser.parse_args()
    if args.child:
        need(args.actual is None and args.out is None, 'single child fixture route')
        child(args.child)
    else:
        need(args.actual is not None and args.out is not None, 'explicit accepted run and control output')
        run(args.actual, args.out)


if __name__ == '__main__':
    main()
