#!/usr/bin/env python3
"""Compile the exact printed-curve comparison using a pinned generic Mathlib context."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, time

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
parser.add_argument('--context', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
parser.add_argument('--module', choices=['WholePopulationComparison2026','RetunedPublishedScalar'],
                    default='WholePopulationComparison2026')
args = parser.parse_args()
context = json.loads(args.context.read_text())
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
if sha(context['compiler']) != context['compiler_sha256']:
    raise RuntimeError('pinned compiler mismatch')
args.out.mkdir(parents=True, exist_ok=False)
src = args.out / (args.module+'.lean')
src.write_bytes((HERE / src.name).read_bytes())
(args.out / 'compile.executed.py').write_bytes(Path(__file__).read_bytes())
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(context['generic_libraries'])
env['PYTHONDONTWRITEBYTECODE'] = '1'
command = ['/usr/bin/prlimit', '--as=68719476736', '--', '/usr/bin/time', '-v',
           context['compiler'], '-j2', '--root=' + str(args.out), '-o',
           str(args.out / (args.module+'.olean')), str(src)]
t0 = time.monotonic()
result = subprocess.run(command, env=env, capture_output=True)
(args.out / 'stdout').write_bytes(result.stdout)
(args.out / 'stderr').write_bytes(result.stderr)
if result.returncode != 0:
    raise RuntimeError('comparison kernel compilation failed')
if any(term in result.stdout for term in [b'sorryAx', b'Lean.ofReduceBool', b'native_decide.ax']):
    raise RuntimeError('unapproved comparison axiom')
receipt = {'status': 'PASS_KERNEL_ALGEBRA_ONLY_NOT_ANALYTIC_SOURCE_PROOF',
           'seconds': time.monotonic()-t0, 'command': command,
           'source_sha256': sha(src), 'object_sha256': sha(args.out / (args.module+'.olean')),
           'compiler_sha256': sha(context['compiler']), 'context_sha256': sha(args.context),
           'compile_script_sha256': sha(args.out / 'compile.executed.py')}
temp = args.out / 'RESULT.json.fresh-tmp'
temp.write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
os.replace(temp, args.out / 'RESULT.json')
print(receipt['status'], receipt['seconds'])
