#!/usr/bin/env python3
"""Exercise the actual offline browser CLI in normal/-O/-OO modes."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--math-count', type=int, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    need(sha(a.input) == a.sha256, 'input identity')
    need(not a.out.exists(), 'fresh controls output required')
    a.out.mkdir(parents=True)
    checker = Path(__file__).with_name('check_draft_report.py')
    rows = []
    for index, flags in enumerate([[], ['-O'], ['-OO']]):
        base = [sys.executable, *flags, str(checker), '--input', str(a.input),
                '--sha256', a.sha256, '--math-count', str(a.math_count)]
        positive = a.out / ('positive-' + str(index))
        cmd = [*base, '--out', str(positive)]
        cp = subprocess.run(cmd, capture_output=True, text=True)
        (a.out / ('positive-' + str(index) + '.stdout')).write_text(cp.stdout)
        (a.out / ('positive-' + str(index) + '.stderr')).write_text(cp.stderr)
        need(cp.returncode == 0, 'actual positive browser CLI: ' + cp.stdout + cp.stderr)
        receipt = json.loads((positive / 'RESULT.json').read_bytes())
        need(receipt['status'] == 'PASS_DRAFT_OFFLINE_DESKTOP_390_MATH_KEYBOARD_REVIEW'
             and receipt['input_sha256'] == a.sha256 and not receipt['issues'], 'positive browser receipt')
        rows.append({'kind': 'positive', 'optimization': flags, 'command': cmd,
                     'returncode': cp.returncode, 'receipt_sha256': sha(positive / 'RESULT.json')})
        for kind in ['wrong-sha', 'unknown-option', 'existing-output']:
            target = positive if kind == 'existing-output' else a.out / (kind + '-' + str(index))
            cmd = [*base, '--out', str(target)]
            expected = 'fresh output required'
            if kind == 'wrong-sha':
                cmd[cmd.index('--sha256') + 1] = '0' * 64
                expected = 'snapshot input identity'
            if kind == 'unknown-option':
                cmd += ['--not-a-browser-option']
                expected = 'unrecognized arguments'
            old = sha(positive / 'RESULT.json')
            cp = subprocess.run(cmd, capture_output=True, text=True)
            need(cp.returncode != 0 and expected in cp.stderr, 'negative browser CLI: ' + kind)
            need(sha(positive / 'RESULT.json') == old, 'negative route changed positive receipt')
            need(kind == 'existing-output' or not target.exists(), 'rejected route created output')
            rows.append({'kind': kind, 'optimization': flags, 'command': cmd,
                         'returncode': cp.returncode, 'expected_rejection': expected,
                         'stdout_sha256': hashlib.sha256(cp.stdout.encode()).hexdigest(),
                         'stderr_sha256': hashlib.sha256(cp.stderr.encode()).hexdigest()})
    need(sha(a.input) == a.sha256, 'input changed during controls')
    result = {'status': 'PASS_ACTUAL_BROWSER_CLI_ALL_THREE_MODES_AND_REJECTION_CONTROLS',
              'checker_sha256': sha(checker), 'controller_sha256': sha(__file__),
              'input_sha256': a.sha256, 'rows': rows,
              'final_report_acceptance': False}
    pending = a.out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, a.out / 'RESULT.json')
    print(result['status'])


if __name__ == '__main__':
    main()
