#!/usr/bin/env python3
"""Actual all-mode preparation/bound checks; no large checker is launched."""
import argparse, json, subprocess, sys
from pathlib import Path
from reproduce_dual import need, publish, sha

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', required=True, type=Path); a = ap.parse_args()
    need(not a.out.exists(), 'Fresh bounded-wrapper controls required'); a.out.mkdir()
    wrapper = HERE / 'reproduce_fft_dag_bounded_v1.py'; records = []
    for mode in range(3):
        flags = ['-' + 'O' * mode] if mode else []
        for cap in [300, 301, 15]:
            command = [sys.executable, *flags, str(wrapper), '--context', '/pinned-context',
                       '--candidate', '/pinned-candidate', '--run', '/fresh-run',
                       '--workers', '12', '--worker-memory-gib', str(cap), '--prepare-command']
            p = subprocess.run(command, capture_output=True, text=True)
            if cap == 300:
                need(p.returncode == 0, 'Actual initial-AS300 command preparation failed')
                v = json.loads(p.stdout)
                need(v['status'] == 'COMMAND_ONLY_NOT_EXECUTED_NOT_ACCEPTANCE'
                     and v['command'][1] == '--as=322122547200', 'Wrong actual AS command')
            else:
                need(p.returncode != 0, 'Invalid AS range accepted')
            records.append(dict(mode=mode, cap=cap, command=command,
                                returncode=p.returncode, stdout=p.stdout, stderr=p.stderr))
    publish(a.out / 'RESULT.json', dict(
        status='PASS3_ALL_MODE_PREPARATION_AND6_BOUND_REJECTIONS_NO_LARGE_RUN', records=records,
        actual_original_checker_not_executed=True, wrapper_sha256=sha(wrapper),
        harness_sha256=sha(Path(__file__))))
    print('PASS initial-AS300 wrapper all-mode3 preparations/6 rejections; no large run')


if __name__ == '__main__':
    main()
