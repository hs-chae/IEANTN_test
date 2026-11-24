#!/usr/bin/env python3
"""Make a real-file generic overlay compatible with strict context/path checks.

The original link overlay remains unchanged. A dedicated complete Mathlib copy
prevents resolved dependency paths escaping the newly registered generic root.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--completed', required=True, type=Path)
    p.add_argument('--out', required=True, type=Path)
    a = p.parse_args()
    need(not a.out.exists(), 'fresh materialized generic context')
    prior = json.loads((a.completed/'RESULT.json').read_text())
    need(prior['status'] == 'PASS_PINNED_GENERIC_COMPLETION_AND_ACTUAL_FAILED_TRIGGER',
         'actual completed generic prerequisite')
    ctx = json.loads((a.completed/'GENERIC_CONTEXT.json').read_text())
    overlay, target = a.completed/'generic', a.out/'generic'
    files = [q for q in overlay.rglob('*') if q.is_file()]
    expected_bytes = sum(q.stat().st_size for q in files)
    need(expected_bytes < 300*(1 << 30) and shutil.disk_usage(a.out.parent).free > 1 << 40,
         'separate owned scratch and free disk budget')
    a.out.mkdir()
    target.mkdir()
    start = time.monotonic()
    copied, total = 0, 0
    for source in files:
        out = target/source.relative_to(overlay)
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, out, follow_symlinks=True)
        need(not out.is_symlink() and source.stat().st_size == out.stat().st_size,
             'owned regular generic snapshot')
        copied += 1
        total += out.stat().st_size
    ctx['generic_dependencies'] = [dict(q, library=str(target)) if q['name'] == 'mathlib'
                                    else q for q in ctx['generic_dependencies']]
    ctx['generic_libraries'] = [q['library'] for q in ctx['generic_dependencies'] if q['library_present']]
    ctx['generic_completion'] = dict(prior['status'] and ctx['generic_completion'],
        materialized=True, original_completion_result_sha256=sha(a.completed/'RESULT.json'),
        materialization_controller_sha256=sha(__file__), original_caches_unchanged=True)
    (a.out/'GENERIC_CONTEXT.json').write_text(json.dumps(ctx, indent=2)+'\n')
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join(ctx['generic_libraries'])
    probe = a.out/'GenericImport.lean'
    probe.write_text('import Mathlib\n#check Real.pi\n')
    command = [ctx['compiler'], '--root='+str(a.out), '-j1', str(probe),
               '-o', str(a.out/'GenericImport.olean')]
    cp = subprocess.run(command, cwd=a.out, env=env, capture_output=True, text=True)
    (a.out/'stdout').write_text(cp.stdout)
    (a.out/'stderr').write_text(cp.stderr)
    need(cp.returncode == 0, 'materialized full Mathlib import')
    result = dict(status='PASS_MATERIALIZED_GENERIC_ONLY_CONTEXT_AND_IMPORT',
        copied_files=copied, bytes=total, context_sha256=sha(a.out/'GENERIC_CONTEXT.json'),
        command=command, returncode=cp.returncode, seconds=time.monotonic()-start,
        original_completion_sha256=sha(a.completed/'RESULT.json'),
        source_controller_sha256=sha(__file__), original_generic_and_application_banks_unchanged=True)
    (a.out/'RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
