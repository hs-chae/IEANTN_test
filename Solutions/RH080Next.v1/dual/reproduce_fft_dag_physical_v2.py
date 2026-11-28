#!/usr/bin/env python3
"""Launch the unchanged fresh FFT checker with explicit unlimited virtual AS.

AS is virtual address space, not the independent physical cgroup budget. This
wrapper changes no source, numerical parameter or mathematical checker.
"""
import argparse, json, os, sys
from pathlib import Path
from reproduce_dual import need, sha
from resume_fft_dag_source_cold import ORIGINAL_DRIVER_SHA

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context', 'candidate', 'run']:
        ap.add_argument('--' + name, type=Path, required=True)
    ap.add_argument('--workers', type=int, default=12)
    ap.add_argument('--worker-virtual-as', choices=['unlimited'], required=True)
    ap.add_argument('--prepare-command', action='store_true'); a = ap.parse_args()
    need(1 <= a.workers <= 32, 'Bounded worker count required')
    original = HERE / 'reproduce_fft_dag_v2.py'
    need(sha(original) == ORIGINAL_DRIVER_SHA, 'Original unchanged checker required')
    command = ['prlimit', '--as=unlimited',
               '--stack=' + str(256 * 2**20), '--', sys.executable, '-u', str(original),
               '--context', str(a.context), '--candidate', str(a.candidate),
               '--run', str(a.run), '--workers', str(a.workers)]
    if a.prepare_command:
        print(json.dumps(dict(status='COMMAND_ONLY_NOT_EXECUTED_NOT_ACCEPTANCE', command=command,
                              virtual_AS_bytes=None,virtual_AS_policy='EXPLICIT_RLIM_INFINITY_WITH_SEPARATE_PHYSICAL_CGROUP',
                              independent_physical_limit_required_bytes=300 * 2**30,
                              original_checker_sha256=ORIGINAL_DRIVER_SHA)))
        return
    from reproduce_dual import load
    if load(a.candidate / 'PLAN.json')['stages'] == 24:
        memberships = Path('/proc/self/cgroup').read_text().splitlines()
        owned = [v.split('::', 1)[1] for v in memberships if v.startswith('0::')]
        need(len(owned) == 1 and owned[0].endswith('.service'), 'Owned cgroup required for N24')
        cg = Path('/sys/fs/cgroup') / owned[0].lstrip('/')
        need((cg / 'memory.max').read_text().strip() == str(300 * 2**30)
             and (cg / 'memory.swap.max').read_text().strip() == '0',
             'N24 requires actual physical300GiB/noSwap cgroup')
    os.execvp(command[0], command)


if __name__ == '__main__':
    main()
