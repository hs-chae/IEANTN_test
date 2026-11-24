#!/usr/bin/env python3
"""Compose the full pinned source recipe; no prebuilt application bank input.

Install the exact generic context from the campaign publication README first.
All outputs are fresh, isolated children of --out. This orchestrator is not PV.
"""
from pathlib import Path
import argparse, json, subprocess, sys

H = Path(__file__).resolve().parent
S = H.parents[1]
R = S.parents[1]

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    out = a.out.resolve()
    if out.exists():
        raise ValueError('fresh experiment-owned output required')
    out.mkdir(parents=True)
    stages = [
        [sys.executable, str(S/'integration/corrected/reproduce.py'),
         '--out', str(out/'primary454')],
        [sys.executable, str(S/'integration/supplement/audit_corrected.py'),
         '--primary', str(out/'primary454'), '--out', str(out/'supplement619'),
         '--jobs', '1', '--memory-gib', '64', '--threads', '2'],
        [sys.executable, str(H/'reproduce_zero.py'),
         '--foundation', str(out/'supplement619'), '--out', str(out/'box660')],
        [sys.executable, str(H/'controls_zero.py'),
         '--run', str(out/'box660'), '--out', str(out/'controls')],
    ]
    for index, command in enumerate(stages):
        cp = subprocess.run(command, cwd=R)
        (out/('stage-'+str(index)+'.json')).write_text(json.dumps(
            {'command': command, 'returncode': cp.returncode}, indent=2)+'\n')
        if cp.returncode != 0:
            raise SystemExit(cp.returncode)
    print('PASS_COMPOSED_CLEAN_BOX_RECIPE')

if __name__ == '__main__':
    main()
