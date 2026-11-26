#!/usr/bin/env python3
"""Fresh replay, or strictly validated extension of our accepted cold base."""
import argparse, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parents[2]
HERE = Path(__file__).resolve().parent
PV = ROOT / 'Solutions/RH080Next.v1/pv'
MODULES = ['FFTZeroSlices', 'FFTZeroSliceCall', 'FFTZeroSliceAudit']

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def atomic(p, value):
    need(not p.exists(), 'Fresh receipt required: ' + str(p))
    t = p.with_name('.' + p.name + '.tmp')
    with t.open('x') as f:
        json.dump(value, f, indent=2, allow_nan=False)
        f.write('\n'); f.flush(); os.fsync(f.fileno())
    try:
        os.link(t, p)
    finally:
        t.unlink()

def validate_base(base, context):
    plan = json.loads((base / 'PLAN.json').read_text())
    result = json.loads((base / 'RESULT.json').read_text())
    need(result['status'] == 'PASS_SOURCE_COLD_HELPER_COMPILATION_ONLY', 'Base did not pass')
    need(result['roots'] == ['FFTCopyAudit'] and result['modules'] == 47, 'Wrong base scope')
    need(plan['generic'] == context['generic_dependencies'], 'Different generic pins')
    need(sha(base / 'reproduce_copy.executed.py') == plan['controller_sha256'], 'Base controller bytes changed')
    for row in plan['source_rows']:
        need(sha(row['origin']) == row['source_sha256'], 'Base source changed: ' + row['module'])
        need(sha(row['snapshot']) == row['source_sha256'], 'Base snapshot changed: ' + row['module'])
        receipt = json.loads((base / (row['module'] + '.COMPILED.json')).read_text())
        need(receipt['exitcode'] == 0, 'Failed base module')
        obj = base / 'objects' / (row['module'].replace('.', '/') + '.olean')
        need(sha(obj) == receipt['object_sha256'], 'Base object changed: ' + row['module'])
        for suffix in ['stdout', 'stderr', 'time']:
            need(sha(base / 'logs' / (row['module'] + '.' + suffix)) == receipt[suffix + '_sha256'], 'Base log changed')
    source = json.loads((base / 'SOURCE_BYTES.json').read_text())
    need(sha(PV / 'fft/w4_fft_recursive.c') == source['source_sha256'], 'C source changed')
    need('COPY_HELPER_SOURCE_EXECUTION_AUDIT_PASS roots=12 closure=' in
         (base / 'logs/FFTCopyAudit.stdout').read_text(), 'Missing base source/axiom gate')
    return plan

def native(run):
    source = PV / 'fft/w4_fft_recursive.c'
    harness = HERE / 'zero_slice_harness.c'
    (run / 'zero_slice_harness.executed.c').write_bytes(harness.read_bytes())
    command = ['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-I', str(source.parent),
               str(harness), '-o', str(run / 'zero_slice_harness')]
    with (run / 'zero_native_compile.stdout').open('xb') as o, (run / 'zero_native_compile.stderr').open('xb') as e:
        p = subprocess.run(command, stdout=o, stderr=e)
    need(p.returncode == 0, 'Actual-source zero harness compile failed')
    p = subprocess.run([str(run / 'zero_slice_harness')], text=True, capture_output=True)
    (run / 'zero_native_run.stdout').write_text(p.stdout)
    (run / 'zero_native_run.stderr').write_text(p.stderr)
    expected = 'PASS actual zero_words slices: 326 cases; seed=58234dd618c34a19; final_seed=faf2f5458e3c02b1\n'
    need(p.returncode == 0 and p.stdout == expected, 'Actual-source zero harness failed')
    atomic(run / 'ZERO_NATIVE.json', dict(status='PASS_RUNTIME_EXERCISE_NOT_PROOF', command=command,
           compiler_version=subprocess.check_output(['cc', '--version'], text=True), source_sha256=sha(source),
           harness_sha256=sha(harness), binary_sha256=sha(run / 'zero_slice_harness'), stdout=p.stdout))

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--context', type=Path, required=True)
    ap.add_argument('--base', type=Path)
    a = ap.parse_args()
    need(not a.run.exists(), 'Fresh run directory required')
    c = json.loads(a.context.read_text())
    need(sha(c['compiler']) == c['compiler_sha256'], 'Compiler bytes changed')
    started = time.monotonic()
    if a.base is None:
        command = [sys.executable, str(HERE / 'reproduce_copy.py'), '--context', str(a.context),
                   '--run', str(a.run), '--root', 'FFTCopyAudit', '--root', 'FFTZeroSliceAudit']
        p = subprocess.run(command)
        need(p.returncode == 0, 'Fresh full source replay failed')
        audit = a.run / 'logs/FFTZeroSliceAudit.stdout'
        mode = 'FRESH_FULL_50_SOURCE_REPLAY'
    else:
        base_plan = validate_base(a.base, c)
        a.run.mkdir(parents=True)
        source, objects, logs = (a.run / n for n in ['source', 'objects', 'logs'])
        for p in [source, objects, logs]:
            p.mkdir()
        rows = []
        for module in MODULES:
            p = PV / 'lean' / (module + '.lean')
            target = source / (module + '.lean')
            target.write_bytes(p.read_bytes())
            rows.append(dict(module=module, origin=str(p), snapshot=str(target), source_sha256=sha(p)))
        atomic(a.run / 'PLAN.json', dict(status='VALIDATED_47_SOURCE_COLD_BASE_PLUS_3_NEW_SOURCES',
               base=str(a.base), base_plan_sha256=sha(a.base / 'PLAN.json'), base_result_sha256=sha(a.base / 'RESULT.json'),
               source_rows=rows, controller_sha256=sha(Path(__file__)), generic=c['generic_dependencies'],
               historical_or_unvalidated_application_fallback=False, memory_ceiling_gib=256))
        (a.run / 'reproduce_zero_slices.executed.py').write_bytes(Path(__file__).read_bytes())
        env = dict(os.environ, LEAN_PATH=':'.join([str(objects), str(a.base / 'objects'), c['generic_lean_path']]))
        for row in rows:
            module = row['module']; target = objects / (module + '.olean')
            command = ['/usr/bin/time', '-v', '-o', str(logs / (module + '.time')), 'prlimit',
                       '--as=' + str(256 * 2**30), '--stack=' + str(256 * 2**20), '--', c['compiler'],
                       '-j1', '--root=' + str(source), '-o', str(target), row['snapshot']]
            t = time.monotonic()
            with (logs / (module + '.stdout')).open('xb') as o, (logs / (module + '.stderr')).open('xb') as e:
                p = subprocess.run(command, cwd=source, env=env, stdout=o, stderr=e)
            need(p.returncode == 0, 'New source compile failed: ' + module)
            atomic(a.run / (module + '.COMPILED.json'), dict(module=module, command=command,
                   exitcode=p.returncode, seconds=time.monotonic()-t, object_sha256=sha(target),
                   stdout_sha256=sha(logs / (module + '.stdout')), stderr_sha256=sha(logs / (module + '.stderr')),
                   time_sha256=sha(logs / (module + '.time'))))
        validate_base(a.base, c)
        for row in rows:
            need(sha(row['origin']) == row['source_sha256'], 'New source changed')
        audit = logs / 'FFTZeroSliceAudit.stdout'
        mode = 'VALIDATED_SOURCE_COLD_47_BASE_PLUS_3_SOURCE_EXTENSION_NOT_FRESH_50'
    need('ZERO_SLICE_SOURCE_AUDIT_PASS roots=10 closure=' in audit.read_text(), 'Missing final zero source/axiom gate')
    native(a.run)
    peak, killed = 0, 0
    for p in (a.run / 'logs').glob('*.time'):
        text = p.read_text()
        m = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', text)
        if m:
            peak = max(peak, int(m.group(1)))
        killed += int('Command terminated by signal 9' in text)
    disk = sum(p.stat().st_size for p in a.run.rglob('*') if p.is_file())
    atomic(a.run / 'ZERO_RESULT.json', dict(status='PASS_ZERO_SLICE_SOURCE_HELPER_ONLY', mode=mode,
           seconds=time.monotonic()-started, peak_process_ram_kib=peak, disk_bytes=disk, sigkill_events=killed,
           typed_axiom_roots=10, universal_full_Call_correctness=True, raw_byte_initializer_replaced=False,
           whole_FFT_PV_complete=False, ANT_consumer_complete=False))
    print((a.run / 'ZERO_RESULT.json').read_text())

if __name__ == '__main__':
    main()
