#!/usr/bin/env python3
"""Continue the complete source-only723 pipeline, preserving all failed attempts.

This coordinator invokes the actual unchanged proof controllers. The final
Ram606 validator recursively checks the complete source/build/run closure.
No application object cache or developer overlay is a generic dependency.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, math, os, subprocess, sys, time

sys.dont_write_bytecode = True

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def finite(value):
        number = float(value)
        need(math.isfinite(number), 'nonfinite JSON number')
        return number
    def invalid(_value):
        raise ValueError('nonfinite JSON constant')
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_float=finite, parse_constant=invalid)

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def save(path, value):
    pending = path.with_name('.'+path.name+'.pending')
    need(not pending.exists(), 'pending receipt collision')
    pending.write_text(json.dumps(value, indent=2)+'\n')
    os.replace(pending, path)

def live(record):
    root = Path('/proc')/str(record['PID'])
    try:
        fields = (root/'stat').read_text().rsplit(')', 1)[1].split()
        return fields[0] != 'Z' and fields[19] == record['proc_start_ticks']
    except FileNotFoundError:
        return False

def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--source-packet', type=Path, required=True)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--primary', type=Path, required=True)
    parser.add_argument('--existing-supplement', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    packet = args.source_packet.resolve()
    manifest = read(packet/'SOURCE_PACKET.json')
    need(manifest['schema'] == 'RH723_PACKET_V1'
         and type(manifest['exact_proof_modules']) is int
         and manifest['exact_proof_modules'] == 723, 'exact723 source packet')
    source = packet/'source'
    paths = [row['path'] for row in manifest['files']]
    need(len(paths) == len(set(paths)) == manifest['file_count'], 'unique complete file rows')
    entries = list(source.rglob('*'))
    need(not any(path.is_symlink() for path in entries), 'no source packet symlinks')
    actual = {str(path.relative_to(source)) for path in entries if path.is_file()}
    need(actual == set(paths), 'exact actual regular-file source inventory')
    for row in manifest['files']:
        candidate = source/row['path']
        path = candidate.resolve()
        need(path.is_relative_to(source) and path.is_file() and not candidate.is_symlink()
             and sha(path) == row['sha256'], 'source packet identity:'+row['path'])
    need(args.context.is_file(), 'explicit installed pinned generic context')
    solution = source/'Solutions/RHOcticPush.v1'
    exporter = load('complete_packet_exporter', solution/'integration/prepare_complete_source_packet.py')
    proof_universe = exporter.check(source, include_ram606=True)
    need(len(proof_universe) == 723 and proof_universe == manifest['proof_universe'],
         'exact723 compiler source identities')
    os.environ['IEANTN_GENERIC_CONTEXT'] = str(args.context.resolve())
    primary_validator = load('clean_primary_validator', solution/'integration/corrected/reproduce.py')
    primary_validator.context()
    out = args.out.resolve()
    need(not out.exists(), 'fresh owned coordinator output')
    need(not out.is_relative_to(packet) and not args.primary.resolve().is_relative_to(packet),
         'separate immutable source packet from execution outputs')
    need(out != args.primary.resolve(), 'coordinator metadata is not the primary output')
    if args.check:
        print('PASS_COMPLETE723_PACKET_CONTEXT_AND_CLEAN_DRIVER_PREFLIGHT')
        return
    out.mkdir(parents=True)
    env = os.environ.copy()
    env['IEANTN_GENERIC_CONTEXT'] = str(args.context.resolve())
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.pop('LEAN_PATH', None)
    stages, children = [], []
    started = time.monotonic()
    save(out/'PLAN.json', {'controller_sha256': sha(__file__),
         'source_packet_sha256': sha(packet/'SOURCE_PACKET.json'),
         'generic_context_sha256': sha(args.context),
         'primary': str(args.primary.resolve()),
         'existing_supplement': str(args.existing_supplement) if args.existing_supplement else None,
         'trust': 'Kernel mathematics, explicit literature inputs; no source-first PV or official receipt.'})

    def phase(name, target, script, arguments):
        target = target.resolve()
        need(script.is_file(), 'actual phase controller')
        command = [sys.executable, str(script), *arguments]
        begin = time.monotonic()
        launch = Path(str(target)+'.LAUNCH.json')
        # A registered live controller may still be checking its inputs before
        # creating its output directory. It must never be launched twice.
        existing = target.exists() or launch.exists()
        actual_command = command
        if not existing:
            target.parent.mkdir(parents=True, exist_ok=True)
            so, se = out/(name+'.stdout'), out/(name+'.stderr')
            with so.open('w') as stdout, se.open('w') as stderr:
                child = subprocess.Popen(command, env=env, stdout=stdout, stderr=stderr)
                children.append({'PID': child.pid,
                    'proc_start_ticks': Path('/proc') .joinpath(str(child.pid), 'stat')
                                         .read_text().rsplit(')', 1)[1].split()[19],
                    'command': command, 'source_sha256': sha(script), 'phase': name})
                save(out/'CHILDREN.json', children)
                returncode = child.wait()
            need(returncode == 0, 'phase process failure:'+name+'; exact logs retained')
        else:
            record = read(launch) if launch.exists() else None
            actual_command = record.get('command') if record is not None else None
            while not (target/'RESULT.json').exists():
                need(not (target/'FAILURE.json').exists(), 'preserved failed phase:'+name)
                need(record is not None and live(record),
                     'registered phase interrupted without a final receipt:'+name)
                need(record.get('controller_sha256') == sha(script),
                     'existing phase source-controller identity')
                save(out/'PROGRESS.json', {'phase': name, 'state': 'waiting for registered own process',
                     'PID': record['PID'], 'elapsed_seconds': time.monotonic()-started})
                time.sleep(10)
        need((target/'RESULT.json').is_file(), 'successful phase must have an atomic receipt')
        receipt = read(target/'RESULT.json')
        need(receipt['controller_sha256'] == sha(script), 'phase receipt controller binding')
        stages.append({'phase': name, 'root': str(target),
            'actual_registered_controller_command': actual_command,
            'requested_command_if_new': command,
            'existing_registered_or_completed_phase': existing,
            'RESULT_sha256': sha(target/'RESULT.json'), 'status': receipt['status'],
            'coordinator_phase_seconds': time.monotonic()-begin,
            'reported_phase_seconds': receipt.get('seconds'),
            'resource_measurements': {key: receipt[key] for key in [
                'peak_child_RSS_KiB', 'peak_individual_child_RSS_KiB',
                'sampled_peak_process_tree_RSS_bytes', 'sampled_peak_owned_disk_bytes']
                if key in receipt}})
        save(out/'STAGES.json', stages)
        return target

    try:
        primary_script = solution/'integration/corrected/reproduce.py'
        primary = phase('primary454', args.primary, primary_script,
                        ['--out', str(args.primary.resolve()), '--memory-gib', '64'])
        available = next(int(line.split()[1])*1024 for line in
                         Path('/proc/meminfo').read_text().splitlines()
                         if line.startswith('MemAvailable:'))
        jobs = min(4, (available//(1 << 30)-512)//64)
        need(jobs >= 1, 'preserve512GiB host reserve before the supplement')
        supplement = args.existing_supplement or out/'supplement'
        basis = phase('supplement165', supplement, solution/'integration/supplement/audit_corrected.py',
                      ['--primary', str(primary), '--out', str(supplement.resolve()),
                       '--jobs', str(jobs), '--memory-gib', '64'])
        for label, relative, dirname in [
            ('box40', 'box/zero/reproduce_zero.py', 'box40'),
            ('closed_box33', 'integration/closed_box/reproduce.py', 'closed-box33'),
            ('spectral19', 'integration/spectral_final/reproduce.py', 'spectral19'),
            ('ram60611', 'integration/ram606/reproduce.py', 'ram60611')]:
            target = out/dirname
            basis = phase(label, target, solution/relative,
                          ['--foundation', str(basis), '--out', str(target)])
        verify = [sys.executable, str(solution/'integration/ram606/reproduce.py'),
                  '--verify', str(basis)]
        check = subprocess.run(verify, env=env, capture_output=True, text=True)
        (out/'final-readback.stdout').write_text(check.stdout)
        (out/'final-readback.stderr').write_text(check.stderr)
        need(check.returncode == 0, 'actual final recursive723 source/readback failed')
        save(out/'RESULT.json', {'status': 'PASS_COMPLETE_SOURCE_ONLY723_PIPELINE',
             'stages': stages, 'source_packet_sha256': sha(packet/'SOURCE_PACKET.json'),
             'generic_context_sha256': sha(args.context), 'controller_sha256': sha(__file__),
             'seconds_including_waits': time.monotonic()-started, 'final_readback_command': verify,
             'final_readback_returncode': check.returncode,
             'readback_stdout_sha256': sha(out/'final-readback.stdout'),
             'readback_stderr_sha256': sha(out/'final-readback.stderr'),
             'resource_scope': 'Per-phase measurements retain their actual scopes. Child maxima '
                               'are not relabelled aggregate process-tree peaks.',
             'primary_used_recovery': read(primary/'RESULT.json').get('resume_source') is not None,
             'source_first_PV_claim': False, 'official_Comparator_receipt': False})
    except BaseException as error:
        save(out/'FAILURE.json', {'error': repr(error), 'completed_phases': len(stages),
             'seconds': time.monotonic()-started,
             'note': 'No failure is retroactively changed or attributed to OOM without evidence.'})
        raise

if __name__ == '__main__':
    main()
