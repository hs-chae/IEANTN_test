#!/usr/bin/env python3
"""Guarded format-only adapter for an independently accepted NEW fresh run."""
import argparse, subprocess, sys
from pathlib import Path
from reproduce_dual import load, need, sha
import verify_fft_dag_fresh as fresh

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['base', 'context', 'candidate', 'accepted', 'run']:
        ap.add_argument('--' + name, required=True, type=Path)
    ap.add_argument('--toy', action='store_true'); a = ap.parse_args()
    gate = load(a.accepted)
    need(gate['status'] == 'PASS_INDEPENDENT_ORIGINAL_W4_FFT_SOURCE_COLD_KERNEL_ONLY'
         and gate['validator_sha256'] == sha(Path(fresh.__file__)),
         'Exact independent fresh-run acceptance required')
    fresh.verify_math(a.base.resolve(), a.context, a.candidate.resolve())
    command = [sys.executable, str(HERE / 'export_fft_dag_bank.py'),
               '--base', str(a.base), '--context', str(a.context),
               '--candidate', str(a.candidate), '--accepted', str(a.accepted),
               '--run', str(a.run), *(['--toy'] if a.toy else [])]
    result = subprocess.run(command)
    need(result.returncode == 0, 'Original fresh format-only export failed')


if __name__ == '__main__':
    main()
