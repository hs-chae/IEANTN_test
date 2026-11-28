#!/usr/bin/env python3
"""Actual all-mode observer failure controls; no mathematical worker runs."""
import argparse, subprocess, sys
from pathlib import Path
from reproduce_dual import load, need, publish, sha

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', required=True, type=Path); a = ap.parse_args()
    need(not a.out.exists(), 'Fresh observer controls required'); a.out.mkdir()
    failed = a.out / 'incomplete-supervisor.json'
    publish(failed, dict(status='INCOMPLETE_NO_MATH_ACCEPTANCE', returncode=-15,
                         failure='Controlled owned interruption'))
    records = []
    script = HERE / 'watch_fft_dag_nested_completion.py'
    for mode in range(3):
        flags = ['-' + 'O' * mode] if mode else []
        observer = a.out / ('observer-' + str(mode)); bank = a.out / ('must-not-export-' + str(mode))
        command = [sys.executable, *flags, str(script), '--run', '/missing-run',
                   '--context', '/missing-context', '--candidate', '/missing-candidate',
                   '--supervisor', str(failed), '--command-plan', '/missing-command',
                   '--stdout', '/missing-stdout', '--stderr', '/missing-stderr',
                   '--observer', str(observer), '--export', str(bank), '--unit', 'test.service']
        p = subprocess.run(command, capture_output=True, text=True)
        need(p.returncode != 0 and (observer / 'FAILURE.json').is_file()
             and not (observer / 'RESULT.json').exists() and not bank.exists(),
             'Observer accepted/exported an incomplete child')
        need(load(observer / 'FAILURE.json')['status'] == 'NO_ACCEPTANCE_FROM_OBSERVER',
             'Missing actual observer failure receipt')
        records.append(dict(mode=mode, command=command, returncode=p.returncode,
                            failure_receipt_sha256=sha(observer / 'FAILURE.json')))
    publish(a.out / 'RESULT.json', dict(
        status='PASS_OBSERVER_ACTUAL_NORMAL_O_OO_INCOMPLETE_CHILD_REJECTION',
        records=records, observer_sha256=sha(script), harness_sha256=sha(Path(__file__)),
        no_mathematical_worker_or_production_data_used=True))
    print('PASS observer rejects incomplete supervised child in all3 modes')


if __name__ == '__main__':
    main()
