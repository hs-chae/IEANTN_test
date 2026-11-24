#!/usr/bin/env python3
"""Compile one exact frozen mathematical source; no native numerical acceptance."""
import hashlib, json, os, pathlib, subprocess, sys, time

S = pathlib.Path(__file__).resolve().parent
D = pathlib.Path('/data/ivy-rh-one-prime-20261124/gaussian-fourier')
C = json.loads(pathlib.Path('/data/ivy-rh-one-prime-20261124/network/Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text())
module, attempt = sys.argv[1:]
out = D / attempt
out.mkdir(parents=True, exist_ok=False)
source = out / (module + '.lean')
source.write_bytes((S / (module + '.lean')).read_bytes())
(D / 'objects').mkdir(exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join([str(D / 'objects'), '/data/ivy-rh-one-prime-20261124/gaussian-kernel/objects', '/data/ivy-rh-octic-20261123/integration/public739-runtime-appends-v1/feedback734/union', *C['generic_libraries']])
cmd = ['/usr/bin/prlimit', '--as=68719476736', '--cpu=1800', '--', '/usr/bin/time', '-v', C['compiler'], '-j1', '--root=' + str(out), str(source), '-o', str(out / (module + '.olean'))]
start = time.monotonic()
with (out / 'stdout').open('w') as stdout, (out / 'stderr').open('w') as stderr:
    result = subprocess.run(cmd, env=env, stdout=stdout, stderr=stderr)
receipt = {'module': module, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'compiler': C['compiler'], 'compiler_sha256': hashlib.sha256(pathlib.Path(C['compiler']).read_bytes()).hexdigest(), 'command': cmd, 'lean_path': env['LEAN_PATH'], 'elapsed_seconds': time.monotonic() - start, 'exit_code': result.returncode}
tmp = out / 'RESULT.json.tmp'
tmp.write_text(json.dumps(receipt, indent=2) + '\n')
tmp.replace(out / 'RESULT.json')
if result.returncode == 0:
    (D / 'objects' / (module + '.olean')).write_bytes((out / (module + '.olean')).read_bytes())
print(json.dumps(receipt))
print((out / 'stdout').read_text()[-16000:])
print((out / 'stderr').read_text()[-1500:])
raise SystemExit(result.returncode)
