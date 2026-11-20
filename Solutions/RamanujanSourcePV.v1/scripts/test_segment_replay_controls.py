#!/usr/bin/env python3
"""Run actual positive/negative receipt CLIs under normal, -O and -OO Python."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

S = Path(__file__).resolve().parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--validator', type=Path, default=S / 'scripts/reproduce_segment_checker.py')
    args = parser.parse_args()
    original = args.receipt.resolve()
    out = args.out.resolve()
    need(not out.exists(), 'fresh controls output required')
    out.mkdir(parents=True)
    (out / 'controller.py').write_bytes(Path(__file__).read_bytes())
    result = json.loads((original / 'RESULT.json').read_text())
    statuses = {'FRESH_SEGMENT_CHECKER_SOURCE_CLOSURE_PASS': 'CHECKED_COMPLETE_SEGMENT_REPLAY',
                'FRESH_SELECTED_SOURCE_CLOSURE_PASS': 'CHECKED_COMPLETE_SELECTED_REPLAY'}
    need(result['status'] in statuses and args.validator.is_file(), 'actual completed receipt/validator')
    accepted_status = statuses[result['status']]
    cases = [('positive', original, True)]
    for name in ['missing_record', 'source_hash', 'axioms', 'old_objects', 'duplicate_key']:
        case = out / name
        case.mkdir()
        (case / 'PLAN.json').write_bytes((original / 'PLAN.json').read_bytes())
        data = json.loads(json.dumps(result))
        if name == 'missing_record':
            data['records'] = data['records'][1:]
        elif name == 'source_hash':
            data['records'][0]['source_sha256'] = '0' * 64
        elif name == 'axioms':
            data['axioms'][next(iter(data['axioms']))].append('Lean.ofReduceBool')
        elif name == 'old_objects':
            data['old_application_objects_used'] = True
        raw = json.dumps(data, indent=2)
        if name == 'duplicate_key':
            raw = raw[:-1] + ',"status":' + json.dumps(result['status']) + '}'
        (case / 'RESULT.json').write_text(raw + '\n')
        cases.append((name, case, False))
    records = []
    for mode in [[], ['-O'], ['-OO']]:
        for name, case, expected in cases:
            label = ('normal' if not mode else mode[0][1:]) + '-' + name
            command = [sys.executable, *mode, str(args.validator.resolve()),
                       '--check', str(case)]
            run = subprocess.run(command, capture_output=True, text=True, check=False)
            (out / (label + '.stdout')).write_text(run.stdout)
            (out / (label + '.stderr')).write_text(run.stderr)
            need((run.returncode == 0) == expected, 'wrong actual CLI verdict ' + label)
            if expected:
                parsed = json.loads(run.stdout)
                need(parsed['status'] == accepted_status, 'actual positive acceptance')
            else:
                need(accepted_status not in run.stdout, 'no negative acceptance output')
                need(not (case / 'CHECKED.json').exists(), 'no acceptance receipt on rejection')
            records.append({'label': label, 'expected_accept': expected,
                            'command': command, 'exit_code': run.returncode,
                            'stdout_sha256': sha(out / (label + '.stdout')),
                            'stderr_sha256': sha(out / (label + '.stderr'))})
    receipt = {'status': 'ACTUAL_SEGMENT_REPLAY_CLI_CONTROLS_PASS', 'records': records,
               'original_result_sha256': sha(original / 'RESULT.json'),
               'validator_sha256': sha(args.validator),
               'controller_sha256': sha(__file__), 'original_artifacts_modified': False}
    temporary = out / 'RESULT.json.tmp'
    temporary.write_text(json.dumps(receipt, indent=2) + '\n')
    temporary.replace(out / 'RESULT.json')
    print(json.dumps({'status': receipt['status'], 'actual_cli_cases': len(records)}, sort_keys=True))


if __name__ == '__main__':
    main()
