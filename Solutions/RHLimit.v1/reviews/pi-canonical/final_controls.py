#!/usr/bin/env python3
"""Run the actual frozen source/math gate with explicit acceptance controls."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys

R = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    need(not a.out.exists(), 'fresh controls output required')
    a.out.mkdir(parents=True)
    frozen = R / 'SCOPE_FINAL.json'
    duplicate = a.out / 'duplicate.json'
    duplicate.write_text('{"stage":"x","stage":"y"}\n')
    wrong = a.out / 'wrong-scope.json'
    wrong.write_text(json.dumps({'stage': 'FROZEN_ROOT_HANDOFF_FOR_FINAL_REVIEW',
                                 'files': [], 'declarations': 53}) + '\n')
    rows = []
    for index, flags in enumerate([[], ['-O'], ['-OO']]):
        target = a.out / ('positive-' + str(index) + '.json')
        cmd = [sys.executable, *flags, str(R / 'final_gate.py'), '--out', str(target)]
        cp = subprocess.run(cmd, capture_output=True, text=True)
        need(cp.returncode == 0, 'positive actual CLI failed: ' + cp.stdout + cp.stderr)
        result = json.loads(target.read_bytes())
        need(result['status'] == 'PASS_FROZEN_CANONICAL_SOURCE_MATH_PRESERVATION_GATE'
             and result['declaration_identities'] == 53, 'positive receipt')
        rows.append({'kind': 'positive', 'flags': flags, 'command': cmd,
                     'returncode': cp.returncode, 'receipt_sha256': sha(target)})
        for kind, scope, reason in [
            ('duplicate-json', duplicate, 'duplicate JSON key'),
            ('omitted-source-pins', wrong, 'Root authorized frozen handoff identity'),
            ('development', R / 'SCOPE_DRAFT.json', 'Root authorized frozen handoff identity'),
            ('unknown-option', frozen, 'unrecognized arguments'),
            ('existing-output', frozen, 'fresh receipt required')]:
            out = target if kind == 'existing-output' else a.out / (kind + '-' + str(index) + '.json')
            cmd = [sys.executable, *flags, str(R / 'final_gate.py'), '--scope', str(scope), '--out', str(out)]
            if kind == 'unknown-option':
                cmd += ['--not-a-source-gate-option']
            before = sha(target)
            cp = subprocess.run(cmd, capture_output=True, text=True)
            need(cp.returncode != 0 and reason in cp.stderr, 'negative actual CLI failed: ' + kind)
            need(sha(target) == before, 'negative route changed accepted receipt')
            need(kind == 'existing-output' or not out.exists(), 'rejected route emitted receipt')
            rows.append({'kind': kind, 'flags': flags, 'command': cmd,
                         'returncode': cp.returncode, 'expected_rejection': reason,
                         'stderr_sha256': hashlib.sha256(cp.stderr.encode()).hexdigest()})
    result = {'status': 'PASS_ALL18_ACTUAL_FROZEN_GATE_ROUTES_NORMAL_O_OO',
              'gate_sha256': sha(R / 'final_gate.py'), 'controller_sha256': sha(__file__),
              'frozen_scope_sha256': sha(frozen), 'rows': rows}
    pending = a.out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, a.out / 'RESULT.json')
    print(result['status'])


if __name__ == '__main__':
    main()
