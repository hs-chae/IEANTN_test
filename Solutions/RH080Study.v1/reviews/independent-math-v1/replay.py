#!/usr/bin/env python3
"""Independent source-closure replay; bounded, sequential, no application cache.

Run from any directory. All output remains beside this test script. Generic
Mathlib and the pre-existing LeanCert library remain explicit trusted providers.
This is ordinary Lean kernel checking, never C-source PV or Comparator approval.
"""
import hashlib, json, os, pathlib, re, subprocess, time

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[3]
STUDY = REPO / 'Solutions/RH080Study.v1'
CTX = json.loads(pathlib.Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text())
GENERIC = CTX['generic_lean_path']
LEANCERT = '/data/ivy-rh-080-20261125/baseline/gaussian53-v1/run/compile/objects'
OUT = HERE / 'fresh-replay'

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

need(not OUT.exists(), 'Fresh output required')
need(sha(pathlib.Path(CTX['compiler'])) == CTX['compiler_sha256'], 'Compiler identity changed')
available = int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))) * 1024
need(available >= 256 * 2**30, 'Host reserve unavailable')
mapping = {
    'ThetaCubeSolution': REPO/'Solutions/ThetaCubePopulation.v1/Solution.lean',
    'ZeroEnvelopeSolution': REPO/'Solutions/ZeroCountEnvelope.v1/Solution.lean',
}
seen, order = set(), []

def visit(module):
    if module.startswith(('Mathlib', 'LeanCert', 'Lean.', 'Std.', 'Init.')) or module in ('Lean', 'Std', 'Init'):
        return
    if module in seen:
        return
    seen.add(module)
    candidates = [mapping.get(module), REPO/(module.replace('.', '/')+'.lean')]
    candidates += [STUDY/p/(module.replace('.', '/')+'.lean') for p in ('functional', 'pv/lean', 'sine', 'estimates')]
    source = next((p for p in candidates if p and p.is_file()), None)
    need(source is not None, 'Missing source '+module)
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                visit(dep)
    order.append((module, source))

for entry in ('CubeConsumerAudit', 'ZeroEnvelopeAudit', 'CompactDualVerified'):
    visit(entry)
OUT.mkdir()
(OUT/'source').mkdir()
(OUT/'objects').mkdir()
(OUT/'logs').mkdir()
rows = []
for module, source in order:
    target = OUT/'source'/(module.replace('.', '/')+'.lean')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(source.read_bytes())
    rows.append(dict(module=module, source=str(source), sha256=sha(source)))
(OUT/'plan.json').write_text(json.dumps(dict(modules=rows, compiler=CTX['compiler'], compiler_sha256=CTX['compiler_sha256'], generic_path=GENERIC, leancert_provider=LEANCERT, preexisting_application_objects=False), indent=2)+'\n')
env = os.environ.copy()
env['LEAN_PATH'] = str(OUT/'objects')+':'+GENERIC+':'+LEANCERT
results = []
started = time.monotonic()
for row in rows:
    module = row['module']
    source = OUT/'source'/(module.replace('.', '/')+'.lean')
    obj = OUT/'objects'/(module.replace('.', '/')+'.olean')
    obj.parent.mkdir(parents=True, exist_ok=True)
    command = ['/usr/bin/prlimit', '--as='+str(64*2**30), '--', '/usr/bin/time', '-v', CTX['compiler'], '-j2', '--root='+str(OUT/'source'), '-o', str(obj), str(source)]
    log = OUT/'logs'/module.replace('.', '_')
    before = time.monotonic()
    run = subprocess.run(command, env=env, capture_output=True)
    log.with_suffix('.stdout').write_bytes(run.stdout)
    log.with_suffix('.stderr').write_bytes(run.stderr)
    results.append(dict(module=module, returncode=run.returncode, seconds=time.monotonic()-before, command=command, object_sha256=sha(obj) if obj.exists() else None))
    (OUT/'progress.json').write_text(json.dumps(results[-1])+'\n')
    need(run.returncode == 0, 'Compiler rejected '+module+': '+run.stdout.decode(errors='replace')[-2000:])
    need(sha(pathlib.Path(row['source'])) == row['sha256'], 'Concurrent source mutation '+module)
    print(module, 'PASS', flush=True)
for row in rows:
    need(sha(pathlib.Path(row['source'])) == row['sha256'], 'Final source identity '+row['module'])
for module, marker in [('CubeConsumerAudit', 'THETA_CUBE_AUDIT_PASS_7'), ('ZeroEnvelopeAudit', 'ZERO_ENVELOPE_AUDIT_PASS_5')]:
    text = (OUT/'logs'/(module+'.stdout')).read_text()
    need(marker in text, 'Missing audit success '+module)
all_logs = '\n'.join(p.read_text() for p in (OUT/'logs').glob('*.stdout'))
need('sorryAx' not in all_logs and 'Lean.ofReduceBool' not in all_logs, 'Forbidden printed axiom')
text = (OUT/'logs'/'CompactDualVerified.stdout').read_text()
need('kernel_compact_obstruction' in text and 'propext' in text, 'Missing functional axiom output')
rss = [int(x) for p in (OUT/'logs').glob('*.stderr') for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)', p.read_text())]
result = dict(status='PASS_SCOPED_FRESH_MATHEMATICAL_SOURCE_CLOSURE', module_count=len(rows), elapsed_seconds=time.monotonic()-started, maximum_recorded_per_process_rss_kib=max(rss), aggregate_peak_not_measured=True, source_first_PV=False, compiler=CTX['compiler'], compiler_sha256=CTX['compiler_sha256'], commands=results)
temporary = OUT/'result.pending'
temporary.write_text(json.dumps(result, indent=2)+'\n')
os.link(temporary, OUT/'result.json')
temporary.unlink()
print(json.dumps({k:v for k,v in result.items() if k!='commands'}))
