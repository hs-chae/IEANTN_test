#!/usr/bin/env python3
"""Exercise real editorial CLIs under normal, -O and -OO Python modes.

This checks report generation and interface guards, never mathematical claims.
Use a fresh output directory outside this source tree.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--render-package', required=True, type=Path)
    ap.add_argument('--browser-executable', type=Path)
    ap.add_argument('--browser-checks', action='store_true')
    a = ap.parse_args()
    source = Path(__file__).resolve().parent
    out = a.out.resolve()
    need(not out.exists() and out != source and source not in out.parents,
         'Use a fresh output directory outside the report sources')
    out.mkdir(parents=True)
    before = json.loads((source / 'SUPPLEMENT_BUILD.json').read_text())
    need(not before['editorial_final_flag'], 'Run draft controls before final stamping')
    revision = before['source_revision']
    owned = ['PAPER_READY_EN.html', 'PAPER_READY_EN.tex',
             'RH080_PAPER_SUMMARY_KO.html', 'SUPPLEMENT_BUILD.json']
    expected = {name: sha(source / name) for name in owned}
    rows = []
    for mode in [[], ['-O'], ['-OO']]:
        label = mode[0].lstrip('-') if mode else 'normal'
        common = [sys.executable, *mode, str(source / 'build_supplement.py'),
                  '--render-package', str(a.render_package)]
        cases = [
            ('render', ['--source-revision', revision, '--followup-status', before['followup_editorial_status']], None),
            ('running_final', ['--source-revision', revision, '--followup-status', 'running', '--final'],
             'Final editorial stamp requires completed follow-up status'),
            ('absent_final_commit', ['--source-revision', '0' * 40,
                                    '--followup-status', 'complete', '--final'],
             "0000000000000000000000000000000000000000:IEANTN/Nodes/GaussianFourierWitness/v3/Conclusions.lean"),
        ]
        for name, args, error in cases:
            command = common + args
            run = subprocess.run(command, capture_output=True, text=True)
            stem = out / (label + '-' + name)
            stem.with_suffix('.stdout').write_text(run.stdout)
            stem.with_suffix('.stderr').write_text(run.stderr)
            need((run.returncode == 0) if error is None else
                 (run.returncode != 0 and error in run.stderr),
                 'Wrong actual CLI result for ' + label + '/' + name)
            actual = {n: sha(source / n) for n in owned}
            need(actual == expected, 'Outputs changed in deterministic/negative controls')
            rows.append({'mode': label, 'case': name, 'command': command,
                         'returncode': run.returncode, 'targeted_error': error,
                         'output_bytes_unchanged': True})
        if a.browser_checks:
            target = out / (label + '-browser')
            command = [sys.executable, *mode, str(source / 'check_layout.py'),
                       '--render-package', str(a.render_package), '--out', str(target)]
            if a.browser_executable:
                command += ['--browser-executable', str(a.browser_executable)]
            run = subprocess.run(command, capture_output=True, text=True)
            (out / (label + '-browser.stdout')).write_text(run.stdout)
            (out / (label + '-browser.stderr')).write_text(run.stderr)
            need(run.returncode == 0 and (target / 'RESULT.json').is_file(),
                 'Actual browser CLI failed in ' + label)
            result = json.loads((target / 'RESULT.json').read_text())
            need(result['status'] == 'PASS_SIX_OFFLINE_FONT_MATHML_MOBILE_DESKTOP_KEYBOARD_AND_ANCHOR_CASES',
                 'Browser acceptance result absent in ' + label)
            rows.append({'mode': label, 'case': 'browser', 'command': command,
                         'returncode': 0, 'receipt_sha256': sha(target / 'RESULT.json')})
    record = {'status': 'PASS_ACTUAL_EDITORIAL_CLI_ROUTES_NORMAL_O_OO',
              'scope': 'Editorial generation/interface checks only; not mathematical verification.',
              'controller_sha256': sha(Path(__file__)), 'source_outputs': expected,
              'browser_checks': a.browser_checks, 'rows': rows}
    temp = out / 'RESULT.pending'
    temp.write_text(json.dumps(record, indent=2) + '\n')
    os.link(temp, out / 'RESULT.json')
    temp.unlink()
    print(json.dumps({'status': record['status'], 'actual_cli_cases': len(rows)}))


if __name__ == '__main__':
    main()
