#!/usr/bin/env python3
"""Actual CLI mutation controls for the new outer-reader's active gates.

These small tests establish reader behavior, not a numerical theorem. Complete
positive full-result readback is required separately after real compilation.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
import data_stage as D
import remaining_stage as R

HERE = Path(__file__).resolve().parent
CASES = ['owned-positive', 'historical-object', 'ancestor-symlink', 'deps-positive',
         'empty-deps', 'omitted-direct', 'foreign-dep', 'generic-app-masquerade',
         'wall-positive', 'wall-one-second', 'duplicate-json', 'overflow-json',
         'value-positive', 'value-endpoint-omitted', 'value-count-float',
         'value-count-bool', 'value-edges-float', 'value-reached-float']
POSITIVE = {'owned-positive', 'deps-positive', 'wall-positive', 'value-positive'}


def execute(case, out):
    own = out/'owned'
    foreign = out/'historical'
    own.mkdir()
    foreign.mkdir()
    (own/'data.olean').write_bytes(b'deterministic-owned-test-object')
    (foreign/'data.olean').write_bytes((own/'data.olean').read_bytes())
    generic = out/'generic'
    generic.mkdir()
    sha = D.sha(own/'data.olean')
    if case in ['owned-positive', 'historical-object', 'ancestor-symlink']:
        actual = str(own/'data.olean')
        expected = own/'data.olean'
        if case == 'historical-object':
            actual = str(foreign/'data.olean')
        if case == 'ancestor-symlink':
            (own/'redirect').symlink_to(foreign, target_is_directory=True)
            actual = str(own/'redirect/data.olean')
            expected = own/'redirect/data.olean'
        D.owned_file(actual, expected, own, sha)
    elif 'deps' in case or case in ['omitted-direct', 'foreign-dep', 'generic-app-masquerade']:
        required = (own/'data.olean').resolve()
        (generic/'Init.olean').write_bytes(b'generic-test-placeholder')
        lines = [str(required), str(generic/'Init.olean')]
        if case == 'empty-deps':
            lines = []
        elif case == 'omitted-direct':
            lines = [str(generic/'Init.olean')]
        elif case == 'foreign-dep':
            lines.append(str(foreign/'data.olean'))
        elif case == 'generic-app-masquerade':
            target = generic/'RamanujanPV/Fake.olean'
            target.parent.mkdir()
            target.write_bytes(b'app-not-generic')
            lines.append(str(target))
        D.dependency_paths(lines, {required: sha}, [generic], {required})
    elif case in ['wall-positive', 'wall-one-second']:
        D.observed_wall('Elapsed (wall clock) time (h:mm:ss or m:ss): 2:13.41\n',
                        133.41297239623964 if case == 'wall-positive' else 1)
    elif case in ['duplicate-json', 'overflow-json']:
        text = '{"count":1,"count":2}' if case == 'duplicate-json' else '{"seconds":1e400}'
        (out/'metadata.json').write_text(text)
        D.read(out/'metadata.json')
    else:
        text = R.audit_source().split('let required := #[', 1)[1].split(']\n', 1)[0]
        endpoints = re.findall(r'`([A-Za-z0-9_.]+)', text)
        value = dict(root='RHOcticPush.ColdCount.complete_actual_source_run', required=endpoints,
                     required_count=12, reached_application_and_boundary_constants=23,
                     checked_value_edges=23)
        if case == 'value-endpoint-omitted':
            value['required'] = value['required'][:-1]
        elif case == 'value-count-float':
            value['required_count'] = 12.0
        elif case == 'value-count-bool':
            value['required_count'] = True
        elif case == 'value-edges-float':
            value['checked_value_edges'] = 23.0
        elif case == 'value-reached-float':
            value['reached_application_and_boundary_constants'] = 23.0
        R.value_payload_check(value)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--case', choices=CASES)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    D.need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(D.ROOT),
           'fresh experiment-owned test output outside source checkout')
    out.mkdir()
    if args.case:
        execute(args.case, out)
        print('ACTIVE_GATE_ACCEPTED')
        return
    rows = []
    for mode in [[], ['-O'], ['-OO']]:
        for case in CASES:
            target = out/(str(len(mode))+'-'+str(len(rows))+'-'+case)
            command = [sys.executable, *mode, str(Path(__file__).resolve()),
                       '--case', case, '--out', str(target)]
            cp = subprocess.run(command, capture_output=True, text=True)
            (out/(str(len(rows))+'.stdout')).write_text(cp.stdout)
            (out/(str(len(rows))+'.stderr')).write_text(cp.stderr)
            accepted = cp.returncode == 0
            D.need(accepted == (case in POSITIVE), 'unexpected actual CLI gate decision:'+case)
            rows.append(dict(case=case, optimization=mode, command=command,
                 returncode=cp.returncode, expected_acceptance=case in POSITIVE,
                 stdout_sha256=D.sha(out/(str(len(rows))+'.stdout')),
                 stderr_sha256=D.sha(out/(str(len(rows))+'.stderr'))))
    D.save(out/'RESULT.json', dict(status='PASS_54_ACTUAL_CLI_OUTER_READER_GATE_CONTROLS',
         test_sha256=D.sha(__file__), data_controller_sha256=D.sha(HERE/'data_stage.py'),
         source_basis_sha256=D.sha(HERE/'source_basis.py'),
         remaining_controller_sha256=D.sha(HERE/'remaining_stage.py'), rows=rows,
         scope='Active pure ownership/dependency/duration/strictJSON/value-census helpers; '
               'full695/305 positive result replay and full-result mutations remain separate.'))
    print('PASS_54_ACTUAL_CLI_OUTER_READER_GATE_CONTROLS')


if __name__ == '__main__':
    main()
