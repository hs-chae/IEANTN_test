#!/usr/bin/env python3
"""Read-only review of final-arm components, separate from the640b proof."""
from pathlib import Path
import datetime, hashlib, json, os, resource, shutil, subprocess, time

B = Path(__file__).resolve().parent
O = B / 'fresh-components-v1'
if O.exists():
    raise ValueError('fresh output required')
(O / 'source').mkdir(parents=True)
(O / 'objects').mkdir()
(O / 'logs').mkdir()
study = Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120')
frozen = study / 'evaluator-private/final-locks/IEANTN_RH/files'
proof = Path('/data/ivy-rh-propagation-20261120/post-lock-verification/Ramanujan640-v1')
config = json.loads((proof / 'BUILD_ENV.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = str(O / 'objects') + ':' + config['LEAN_PATH']
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
modules = ['SharedRH', 'FullRH', 'RamAlgebra', 'CoefficientPV', 'GapFromSource', 'RealCrossing', 'CrossingBracket']
for name in modules:
    shutil.copyfile(frozen / (name + '.lean'), O / 'source' / (name + '.lean'))
shutil.copyfile(frozen / 'rh_coeff.c', O / 'source/rh_coeff.c')
result = {'schema': 'FINAL_FULL_RAMANUJAN_COMPONENT_REVIEW_REPLAY_V1',
    'status': 'RUNNING', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Exact7 final locked Lean sources, not the written610b proof or Python soundness.',
    'model_calls': 0, 'modules': [], 'unchanged_rh_coeff_sha256': sha(frozen / 'rh_coeff.c'),
    'compiled_dependencies_explicit': config, 'source_first_PV_claim': 'Parent source audit decides actual C boundary; this receipt proves compilation and standard axioms only.'}
try:
    for name in modules:
        src = O / 'source' / (name + '.lean')
        cmd = [config['compiler'], '--root=' + str(O / 'source'), '-j8', '-o', str(O / 'objects' / (name + '.olean')), str(src)]
        started = time.monotonic()
        run = subprocess.run(cmd, cwd=O / 'source', env=env, capture_output=True, text=True)
        row = {'module': name, 'source_sha256': sha(src), 'frozen_source_sha256': sha(frozen / (name + '.lean')), 'command': cmd,
            'returncode': run.returncode, 'elapsed_seconds': time.monotonic() - started,
            'peak_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
            'stdout': run.stdout, 'stderr': run.stderr}
        result['modules'].append(row)
        (O / 'logs' / (name + '.json')).write_text(json.dumps(row, indent=2) + '\n')
        if run.returncode or row['source_sha256'] != row['frozen_source_sha256']:
            raise ValueError('component compile or identity failed: ' + name)
        if any(v in run.stdout for v in ['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler']):
            raise ValueError('nonstandard printed proof trust: ' + name)
        print('PASS', name, row['elapsed_seconds'], flush=True)
    result['status'] = 'PASS_EXACT_FINAL_7_COMPONENTS_FRESH_STANDARD_AXIOMS'
except Exception as error:
    result['status'] = 'FAILED_OR_PARTIAL_NO_COMPONENT_ACCEPTANCE'
    result['error'] = str(error)
(O / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
print(result['status'], flush=True)
if not result['status'].startswith('PASS_'):
    raise SystemExit(1)
