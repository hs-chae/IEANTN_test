#!/usr/bin/env python3
"""Build missing pinned generic objects in an owned complete Mathlib overlay.

Never writes an existing generic cache or any application bank/source. The
selected source inventory and actual complete-Mathlib import are separate gates.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def save(path, value):
    tmp = Path(str(path)+'.pending')
    tmp.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(tmp, path)

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--preflight', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--failed-application', required=True, type=Path)
    a = ap.parse_args()
    m, out = read(a.preflight), a.out.resolve()
    need(not out.exists(), 'fresh experiment-owned generic completion output')
    ctx = m['context']
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'pinned compiler')
    available = next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= 576*(1 << 30), '512GiB host reserve plus64GiB job cap')
    need(shutil.disk_usage(out.parent).free >= 1 << 40, 'separate free disk allowance')
    mathlib = next(x for x in ctx['generic_dependencies'] if x['name'] == 'mathlib')
    library, source_root = Path(mathlib['library']), Path(mathlib['path'])
    out.mkdir()
    overlay = out/'generic'
    overlay.mkdir()
    linked = 0
    for source in library.rglob('*'):
        if not source.is_file():
            continue
        target = overlay/source.relative_to(library)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(source.resolve())
        linked += 1
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(overlay), *ctx['generic_libraries']])
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    logs = out/'logs'
    logs.mkdir()
    rows = []
    started = time.monotonic()
    for row in m['missing_objects']:
        need(row['module'].startswith('Mathlib.'), 'only scoped Mathlib completion')
        source = Path(row['source'])
        need(sha(source) == row['source_sha256'], 'pinned missing source')
        stem = overlay/Path(*row['module'].split('.'))
        stem.parent.mkdir(parents=True, exist_ok=True)
        # Remove OWN symlinks before writing any output: never follow a link
        # into the original cache if another job completed that module meanwhile.
        for target in stem.parent.glob(stem.name+'.*'):
            need(target.is_symlink(), 'only an owned overlay link may be replaced')
            target.unlink()
        obj = stem.with_suffix('.olean')
        cmd = ['/usr/bin/prlimit', '--as='+str(64 << 30), '--', '/usr/bin/time', '-v',
               '-o', str(logs/(row['module']+'.resources')), ctx['compiler'],
               '--root='+str(source_root), '-j1', str(source), '-o', str(obj),
               '-i', str(stem.with_suffix('.ilean'))]
        t = time.monotonic()
        with (logs/(row['module']+'.stdout')).open('w') as so, \
             (logs/(row['module']+'.stderr')).open('w') as se:
            cp = subprocess.run(cmd, cwd=source_root, env=env, stdout=so, stderr=se)
        need(sha(source) == row['source_sha256'], 'source unchanged during generic compilation')
        result = dict(module=row['module'], command=cmd, returncode=cp.returncode,
            seconds=time.monotonic()-t, source_sha256=row['source_sha256'],
            logs={suffix: sha(logs/(row['module']+'.'+suffix))
                  for suffix in ['stdout', 'stderr', 'resources']})
        if cp.returncode == 0:
            result['artifacts'] = [dict(path=str(q), sha256=sha(q), bytes=q.stat().st_size)
                for q in stem.parent.glob(stem.name+'.*') if q.is_file() and not q.is_symlink()]
        rows.append(result)
        save(out/'BUILD.json', dict(status='RUNNING' if cp.returncode == 0 else 'FAIL', modules=rows))
        need(cp.returncode == 0, 'generic source compilation failed: '+row['module'])
        print(len(rows), len(m['missing_objects']), row['module'], round(result['seconds'], 2), flush=True)
    for row in m['modules']:
        obj = overlay/Path(*row['module'].split('.')).with_suffix('.olean')
        if row['module'].startswith('Mathlib.'):
            need(obj.is_file(), 'complete selected Mathlib object population')
        else:
            need(Path(row['object']).is_file(), 'complete other selected generic object')
    probe = out/'GenericImport.lean'
    probe.write_text('import Mathlib\n#check Real.pi\n')
    cmd = [ctx['compiler'], '--root='+str(out), '-j1', str(probe), '-o', str(out/'GenericImport.olean')]
    cp = subprocess.run(cmd, cwd=out, env=env, capture_output=True, text=True)
    (out/'GenericImport.stdout').write_text(cp.stdout)
    (out/'GenericImport.stderr').write_text(cp.stderr)
    need(cp.returncode == 0, 'actual full Mathlib import probe failed')
    # Replay the exact observed trigger into our scratch, with the preserved
    # completed application prefix read-only. It is a prerequisite probe only.
    app = a.failed_application.resolve()
    source = app/'source/OcticQuadrature.lean'
    before = sha(source)
    env['LEAN_PATH'] = ':'.join([str(app/'union'), str(overlay), *ctx['generic_libraries']])
    cmd = ['/usr/bin/prlimit', '--as='+str(64 << 30), '--', '/usr/bin/time', '-v',
           '-o', str(out/'OcticQuadrature.resources'), ctx['compiler'], '--root='+str(app/'source'),
           '-j1', str(source), '-o', str(out/'OcticQuadrature.olean')]
    cp = subprocess.run(cmd, cwd=app/'source', env=env, capture_output=True, text=True)
    (out/'OcticQuadrature.stdout').write_text(cp.stdout)
    (out/'OcticQuadrature.stderr').write_text(cp.stderr)
    need(sha(source) == before and cp.returncode == 0, 'exact observed application trigger replay')
    new_context = dict(ctx)
    new_context['generic_libraries'] = [str(overlay), *ctx['generic_libraries']]
    new_context['generic_completion'] = dict(preflight_sha256=sha(a.preflight),
        source_controller_sha256=sha(__file__), fresh_generic_modules=[q['module'] for q in rows],
        overlay=str(overlay), original_caches_unchanged=True, application_objects_unchanged=True)
    save(out/'GENERIC_CONTEXT.json', new_context)
    save(out/'RESULT.json', dict(status='PASS_PINNED_GENERIC_COMPLETION_AND_ACTUAL_FAILED_TRIGGER',
        original_preflight_sha256=sha(a.preflight), linked_original_generic_files=linked,
        selected_generic_modules=len(m['modules']), new_generic_builds=rows,
        complete_Mathlib_import_returncode=0, actual_OcticQuadrature_returncode=0,
        original_application_source_sha256=before, probe_object_sha256=sha(out/'OcticQuadrature.olean'),
        new_context_sha256=sha(out/'GENERIC_CONTEXT.json'), seconds=time.monotonic()-started,
        generic_cache_or_accepted_application_mutation=False,
        scope='Generic prerequisite completion and exact failed application-trigger probe; preserved old80 prefix still needs the separate complete clean resume acceptance.'))
    print('PASS_PINNED_GENERIC_COMPLETION_AND_ACTUAL_FAILED_TRIGGER', flush=True)

if __name__ == '__main__':
    main()
