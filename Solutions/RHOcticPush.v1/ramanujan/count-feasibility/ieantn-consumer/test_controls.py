#!/usr/bin/env python3
"""Actual readback CLI controls, run only after the fresh append passes."""
from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess
import sys
import time
import reproduce as V


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    actual, out = args.run.resolve(), args.out.resolve()
    result = V.read(actual/'RESULT.json')
    V.need(result['status'] == V.STATUS and result['controller_sha256'] == V.sha(V.__file__),
           'completed actual current four-source append required')
    V.need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(actual),
           'fresh separate controls directory')
    watched = ['RESULT.json', 'reproduce.executed.py', 'SOURCE_CLOSURE.executed.json',
               'GENERIC_CONTEXT.executed.json', 'RESOURCE_ADMISSION.json']
    watched += [str(path.relative_to(actual)) for directory in ['source', 'objects', 'logs', 'dependencies']
                for path in (actual/directory).rglob('*') if path.is_file() and not path.is_symlink()]
    original = {name: V.sha(actual/name) for name in watched}
    out.mkdir()
    rows = []
    started = time.monotonic()
    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        for kind in ['positive', 'rehashed_source', 'rehashed_output', 'false_exact_target',
                     'wrong_timed_argv', 'symlink_context', 'symlink_log', 'symlink_dependency']:
            label = mode+'-'+kind
            case = out/label
            case.mkdir()
            target = actual
            expected = None
            if kind != 'positive':
                target = case/'mutation-fixture'
                shutil.copytree(actual, target, symlinks=True)
                forged = V.read(target/'RESULT.json')
                if kind == 'rehashed_source':
                    path = target/'source/WordBytesBounded.lean'
                    path.write_bytes(path.read_bytes()+b'\n-- control: changed frozen source\n')
                    row = next(x for x in forged['compilations'] if x['module'] == 'WordBytesBounded')
                    row['source_sha256'] = V.sha(path)
                    expected = 'frozen append source:WordBytesBounded'
                elif kind in ['rehashed_output', 'false_exact_target']:
                    path = target/'logs/IEANTNCountConsumerAudit.stdout'
                    lines = [line for line in path.read_text().splitlines()
                             if 'IEANTN_COUNT_VALUE_PATH {' in line]
                    V.need(len(lines) == 1, 'one original actual VALUE output to mutate')
                    if kind == 'rehashed_output':
                        path.write_text(path.read_text()+'\n'+lines[0]+'\n')
                        expected = 'one actual IEANTN VALUE payload'
                    else:
                        prefix, raw = lines[0].split('IEANTN_COUNT_VALUE_PATH ', 1)
                        value = json.loads(raw)
                        value['exact_target_checked'] = False
                        path.write_text(path.read_text().replace(lines[0], prefix+'IEANTN_COUNT_VALUE_PATH '+
                            json.dumps(value, separators=(',', ':')), 1))
                        expected = 'complete exact same-run/grammar/correctness/byte VALUE audit'
                    row = next(x for x in forged['compilations'] if x['module'] == 'IEANTNCountConsumerAudit')
                    row['stdout_sha256'] = V.sha(path)
                elif kind == 'wrong_timed_argv':
                    path = target/'logs/WordBytesBounded.resources'
                    text, replacements = re.subn(r'Command being timed: "[^\n]+"',
                        'Command being timed: "/bin/false"', path.read_text())
                    V.need(replacements == 1, 'one actual GNU command to mutate')
                    path.write_text(text)
                    row = next(x for x in forged['compilations'] if x['module'] == 'WordBytesBounded')
                    row['resources_sha256'] = V.sha(path)
                    expected = 'actual GNU timed compiler argv'
                else:
                    name = {'symlink_context': 'GENERIC_CONTEXT.executed.json',
                            'symlink_log': 'logs/WordBytesBounded.stdout',
                            'symlink_dependency': 'dependencies/WordBytesBounded.stdout'}[kind]
                    path = target/name
                    V.owned_regular(target, path)
                    path.unlink()
                    path.symlink_to(actual/name)
                    expected = 'owned regular nonsymlink artifact:'+name
                V.save(target/'RESULT.json', forged)
            command = [sys.executable, *flags, '-B', str(Path(V.__file__).resolve()), '--verify', str(target)]
            begin = time.monotonic()
            cp = subprocess.run(command, capture_output=True, text=True)
            (case/'stdout.txt').write_text(cp.stdout)
            (case/'stderr.txt').write_text(cp.stderr)
            if expected is None:
                V.need(cp.returncode == 0 and 'PASS_IEANTN_SAME_RUN_BYTE_CONSUMER_READBACK' in cp.stdout,
                       'actual positive readback:'+label)
            else:
                V.need(cp.returncode != 0 and expected in cp.stderr and
                       'PASS_IEANTN_SAME_RUN_BYTE_CONSUMER_READBACK' not in cp.stdout,
                       'specific source/output mutation rejection:'+label)
                V.need(not (target/'CANDIDATE.json').exists(), 'no acceptance candidate on rejected view')
            receipt = dict(case=label, command=command, returncode=cp.returncode,
                seconds=time.monotonic()-begin, expected_rejection=expected,
                stdout_sha256=V.sha(case/'stdout.txt'), stderr_sha256=V.sha(case/'stderr.txt'),
                fixture_result_sha256=V.sha(target/'RESULT.json'),
                mutation_fixture_is_proof_evidence=False, proof_recompilation=False)
            V.save(case/'RECEIPT.json', receipt)
            rows.append(dict(case=label, receipt=label+'/RECEIPT.json',
                             receipt_sha256=V.sha(case/'RECEIPT.json')))
            print(label, cp.returncode, flush=True)
    V.need(len(rows) == 24 and {name: V.sha(actual/name) for name in watched} == original,
           'all24 distinct CLI cases and unchanged actual accepted run')
    result = dict(status='PASS_ALL24_NORMAL_O_OO_ACTUAL_IEANTN_CONSUMER_CONTROLS',
        source_sha256=V.sha(__file__), checker_sha256=V.sha(V.__file__),
        actual_RESULT_sha256=V.sha(actual/'RESULT.json'), positive=3,
        rehashed_source_rejections=3, rehashed_output_rejections=3,
        false_exact_target_rejections=3, wrong_timed_argv_rejections=3,
        owned_context_log_dependency_rejections=9,
        seconds=time.monotonic()-started, cases=rows, accepted_run_unchanged=True,
        scope='Actual readback of the same compiled append; no additional proof compilation or native run.')
    V.save(out/'RESULT.json', result)
    print(result['status'])


if __name__ == '__main__':
    main()
