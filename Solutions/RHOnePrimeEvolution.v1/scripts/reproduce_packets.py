#!/usr/bin/env python3
"""Run both self-contained source packets using an explicit generic context.
Each underlying full pipeline was independently executed; --check-only invokes
the actual child CLIs without compiling. No old application objects are reused.
"""
import argparse,json,subprocess,sys
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--run-root',type=Path);p.add_argument('--jobs',type=int,default=2);p.add_argument('--check-only',action='store_true');a=p.parse_args();S=Path(__file__).resolve().parents[1];c=json.loads(a.context.read_text())
 if a.jobs not in (1,2,3,4):raise ValueError('Supported workers:1..4')
 if not a.check_only:
  if a.run_root is None or a.run_root.exists():raise ValueError('Fresh --run-root required')
  a.run_root.mkdir(parents=True)
 for name,packet in [('frontier300',S/'portable'),('gaussian53',S/'gaussian_gap/portable')]:
  command=[sys.executable,str(packet/'reproduce.py'),'--compiler',c['compiler'],'--generic-lean-path',c['generic_lean_path'],'--jobs',str(a.jobs)]
  if a.check_only:command+=['--check-only']
  else:command+=['--run',str((a.run_root/name).resolve())]
  subprocess.run(command,check=True)
if __name__=='__main__':
 try:main()
 except (ValueError,OSError,subprocess.CalledProcessError) as e:raise SystemExit(str(e))
