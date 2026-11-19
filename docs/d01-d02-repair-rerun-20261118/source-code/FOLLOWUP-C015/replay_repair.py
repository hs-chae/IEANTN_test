"""Run the repaired and retained certificates from /work/submission."""
from pathlib import Path
import os, subprocess, sys
assert not sys.flags.optimize
p=Path('/usr/bin/python3.10')
e=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
e.pop('PYTHONOPTIMIZE',None)
cmds=[
    ['/usr/bin/g++','-O3','-std=c++17','count.cpp','-o','/work/d01-count'],
    ['/work/d01-count'],
    *[[str(p),*s] for s in [('analytic.py',),('ramanujan.py',),('mertens.py',),
        ('mertens.py','scan'),('bias_repair.py',),('density_repair.py',),
        ('ramanujan_orders.py','tight'),('comparison_repair.py',)]]
]
args=set(sys.argv[1:])
for cmd in cmds:
    if args and not args.intersection(cmd):continue
    print('COMMAND:',*cmd,flush=True)
    r=subprocess.run(cmd,env=e)
    print('EXIT:',r.returncode,flush=True)
    assert r.returncode==0
