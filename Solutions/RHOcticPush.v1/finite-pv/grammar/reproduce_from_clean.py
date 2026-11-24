#!/usr/bin/env python3
"""Compose clean application-source regeneration plus independent grammar checks.

Install the pinned generic Lean/mathlib context first. No historical application
proof object is an input. Numerical count verification is a separate campaign.
"""
from pathlib import Path
import argparse,json,subprocess,sys
H=Path(__file__).resolve().parent
R=H.parents[3]
BASE=R/'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/reproduce_application.py'

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--context',type=Path)
    a=p.parse_args();out=a.out.resolve()
    if out.exists():raise ValueError('Fresh experiment-owned output required')
    out.mkdir(parents=True)
    first=[sys.executable,str(BASE),'--out',str(out/'application32')]
    if a.context:first+=['--context',str(a.context.resolve())]
    commands=[first,
      [sys.executable,str(H/'reproduce.py'),'--foundation',str(out/'application32'),
       '--out',str(out/'grammar5')],
      [sys.executable,str(H/'controls.py'),'--run',str(out/'grammar5'),
       '--out',str(out/'controls')]]
    for n,cmd in enumerate(commands):
        cp=subprocess.run(cmd,cwd=R)
        (out/f'stage-{n}.json').write_text(json.dumps({'command':cmd,'returncode':cp.returncode},indent=2)+'\n')
        if cp.returncode!=0:raise SystemExit(cp.returncode)
    print('PASS_COMPOSED_CLEAN_COUNTER_GRAMMAR_RECIPE')
if __name__=='__main__':main()
