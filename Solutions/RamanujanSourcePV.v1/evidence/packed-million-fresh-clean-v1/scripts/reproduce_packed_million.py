#!/usr/bin/env python3
"""Fixed packed-million sources: regenerate, stage, then optionally cold-replay.

Preparation is explicitly not mathematical acceptance. The frozen guarded
backend supplies the complete proof/object/axiom acceptance and resource policy.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from reproduce_guarded_coupled_closure import strict_json, need, sha
from execute_demand_high_resource import DiskMeter

S = Path(__file__).resolve().parents[1]
NETWORK = S.parents[1]
EVIDENCE = S / 'evidence/packed-numerical-source-v1'
PYTHON = [sys.executable] + (['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else [])


def streamed_sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()


def atomic(path, value):
    temporary = path.with_name(path.name + '.pending')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--prepared-root', type=Path)
    parser.add_argument('--bound-result', action='store_true')
    parser.add_argument('--plan-only', action='store_true')
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--cpus', default='84,85,86,87,88,89')
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    backend = S / 'scripts/reproduce_guarded_coupled_closure.py'
    if args.check:
        need(args.out is None and args.prepared_root is None and not args.plan_only and not args.bound_result,
             'read-only check is a separate mode')
        directory = args.check.resolve()
        result = strict_json(directory / 'RESULT.json')
        need(result['status'] == 'COMPLETE_CLEAN_PACKED_MILLION_SOURCE_REPLAY', 'completed proof run required')
        modules = result['modules']
        need(type(modules) is int and modules in [548, 549], 'exact completed mathematical population')
        lock_path = EVIDENCE / ('BOUND_SOURCE_LOCK.json' if modules == 549 else 'FULL_SOURCE_LOCK.json')
        lock = strict_json(lock_path)
        need(streamed_sha(lock_path) == result['source_lock_sha256'], 'exact preserved source lock')
        need(sha(directory / 'frontend.py') == result['script_sha256'] == sha(Path(__file__)),
             'current and executed frontend source identity')
        need(result['helper_sha256'] == sha(backend) == sha(directory / 'build/controller.py'),
             'current and executed proof acceptance backend')
        plan = strict_json(directory / 'build/PLAN.json')
        prepared = strict_json(directory / 'PREPARED.json')
        need(prepared['modules'] == modules and prepared['source_lock_sha256'] == result['source_lock_sha256'],
             'exact prepared-source population')
        need(plan['targets'] == [lock['root']] and plan['selected_theorems'] == lock['theorems'],
             'actual final consumer and complete theorem population')
        need(plan['script_sha256'] == result['helper_sha256'], 'actual backend plan identity')
        expected = {row['module']: row['source_sha256'] for row in lock['modules']}
        actual = {row['module']: row['source_sha256'] for row in plan['modules']}
        need(len(expected) == len(actual) == len(plan['modules']) == modules and actual == expected,
             'every exact locked application module and source')
        need(streamed_sha(directory / 'build/RESULT.json') == result['build_result_sha256'], 'final backend receipt')
        build = strict_json(directory / 'build/RESULT.json')
        records = build['records']
        need(len(records) == modules + 1 and records[-1]['module'] == 'RamanujanPV.SelectedReplayAudit',
             'all locked application records plus the exact final auditor')
        need({row['module']: row['source_sha256'] for row in records[:-1]} == expected,
             'actual successful compile population matches source lock')
        need(subprocess.call([*PYTHON, str(backend), '--check', str(directory / 'build')]) == 0,
             'actual complete source/object/payload/axiom readback')
        print(json.dumps({'status': 'CHECKED_COMPLETE_CLEAN_PACKED_MILLION_SOURCE_REPLAY'}))
        return
    need(args.out is not None, 'fresh output required')
    context = strict_json(args.context)
    scratch = Path(context['new_application_object_root']).resolve().parent
    out = args.out.resolve()
    need(out.is_relative_to(scratch) and not out.exists() and out.parent.is_dir(), 'fresh context-owned output')
    cpus = [int(value) for value in args.cpus.split(',')]
    need(len(cpus) == len(set(cpus)) and set(cpus) <= os.sched_getaffinity(0), 'actual distinct CPUs')
    need(1 <= args.jobs <= len(cpus) <= 8, 'bounded replay concurrency')
    lock_path = EVIDENCE / ('BOUND_SOURCE_LOCK.json' if args.bound_result else 'FULL_SOURCE_LOCK.json')
    lock = strict_json(lock_path)
    expected_count = 549 if args.bound_result else 548
    need(lock['source_module_count'] == len(lock['modules']) == expected_count, 'entire fixed source closure')
    need(lock['root'] == ('RamanujanPV.PackedSieveResult' if args.bound_result else 'RamanujanPV.PackedSieveMillion'),
         'fixed original mathematical consumer')
    need(len({row['module'] for row in lock['modules']}) == expected_count, 'distinct module identities')
    need(all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', row['module'])
             for row in lock['modules']), 'exact safe compiler module identities')
    need(sha(backend) == lock['guarded_driver_sha256'], 'unchanged guarded proof acceptance backend')
    need(sha(context['compiler']) == context['compiler_sha256'] == lock['compiler_sha256'], 'exact compiler')
    meter = DiskMeter(scratch, 15 << 30)

    def resources():
        available = int(next(row.split()[1] for row in Path('/proc/meminfo').read_text().splitlines()
                             if row.startswith('MemAvailable:'))) * 1024
        disk = meter.measure(force=True)
        need(available >= 1024**4 and available >= (512 + 300) << 30, 'actual RAM and host reserve')
        need(disk.get('error') is None and disk['free_bytes'] >= 1024**4 and
             disk['allocated_bytes'] + disk['forecast_bytes'] <= 300 << 30,
             'independent disk allowance and forecast')
        return {'available_ram_bytes': available, 'disk': disk}

    initial = resources()
    out.mkdir()
    frontend_sha = sha(Path(__file__))
    (out / 'frontend.py').write_bytes(Path(__file__).read_bytes())
    started = time.monotonic()
    stopped = []
    commands = []
    for sig in [signal.SIGUSR1, signal.SIGTERM, signal.SIGINT]:
        signal.signal(sig, lambda number, _frame: stopped.append(number))

    def checkpoint():
        if stopped:
            atomic(out / 'CHECKPOINT.json', {'status': 'DRAINED_PREPARATION_NOT_PROOF_ACCEPTANCE',
                   'signals': stopped, 'commands': commands})
            raise SystemExit(3)

    def run(script, arguments, proof=False):
        checkpoint()
        command = [*PYTHON, str(script), *map(str, arguments)]
        index = len(commands)
        stdout = out / f'command-{index:02d}.stdout'
        stderr = out / f'command-{index:02d}.stderr'
        begin = time.monotonic()
        with stdout.open('w') as so, stderr.open('w') as se:
            previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK,
                {signal.SIGUSR1, signal.SIGTERM, signal.SIGINT})
            try:
                checkpoint()
                def child_setup():
                    os.sched_setaffinity(0, set(cpus))
                    signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
                child = subprocess.Popen(command, stdout=so, stderr=se, preexec_fn=child_setup)
            finally:
                signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
            forwarded = False
            while child.poll() is None:
                # Preparation finishes its current child; the proof controller
                # receives a drain only after it has installed its scheduler.
                if proof and stopped and not forwarded and (out / 'build/RUN_STATE.json').exists():
                    child.send_signal(signal.SIGUSR1)
                    forwarded = True
                time.sleep(0.1)
        commands.append({'command': command, 'exit_code': child.returncode,
                         'seconds': time.monotonic() - begin,
                         'script_sha256': sha(script),
                         'stdout_sha256': streamed_sha(stdout), 'stderr_sha256': streamed_sha(stderr)})
        atomic(out / 'COMMANDS.json', commands)
        checkpoint()
        need(child.returncode == 0, 'actual child completion: ' + script.name)

    prepared = args.prepared_root.resolve() if args.prepared_root else out / 'prepared-baseline'
    if not args.prepared_root:
        run(S / 'scripts/reproduce_local_million.py', ['--context', args.context.resolve(),
            '--out', prepared, '--mode', 'full', '--prepare-only', '--jobs', args.jobs,
            '--memory-gib', 48, '--cpus', args.cpus])
    generated = strict_json(prepared / 'GENERATED_SOURCES.json')
    need(generated['exact_accepted_bytes_checked'] is True and generated['mode'] == 'full',
         'fixed original baseline regeneration, without importing its old proof objects')
    source_map = {row['module']: row for row in generated['sources']}
    need(len(source_map) == len(generated['sources']), 'distinct prepared source identities')
    regenerated = out / 'packed-proposals'
    run(S / 'scripts/generate_packed_sieve_primitive.py', ['--mask-only', '--out', regenerated])
    proposal = strict_json(regenerated / 'PRIMITIVE_PROPOSAL.json')
    mask_map = {row['module']: regenerated / 'source' / Path(*row['module'].split('.')).with_suffix('.lean')
                for row in proposal['primitive_records']}
    need(len(proposal['primitive_records']) == len(mask_map) == 2 and set(mask_map) ==
         {'RamanujanPV.PackedSievePrimitiveMaskMillion', 'RamanujanPV.PackedSievePrimitiveQWindow'},
         'both exact fixed numerical sources must actually regenerate')
    staged = out / 'source'
    staged.mkdir()
    copied = []
    for row in lock['modules']:
        checkpoint()
        module = row['module']
        if row['kind'] == 'tracked':
            source = (NETWORK / row['network_relative_source']).resolve()
            need(source.is_relative_to(NETWORK), 'tracked source remains in the network')
        elif module in mask_map:
            source = mask_map[module]
        elif row['kind'] == 'published':
            source = (NETWORK / row['network_relative_source']).resolve()
            need(source.is_relative_to(EVIDENCE), 'published numerical source remains in its packet')
        else:
            need(module in source_map, 'original generated dependency: ' + module)
            source = Path(source_map[module]['source']).resolve()
            need(source.is_relative_to(prepared), 'prepared source provenance')
        need(streamed_sha(source) == row['source_sha256'], 'exact scientific source: ' + module)
        if row['kind'] != 'tracked':
            if len(copied) % 16 == 0:
                resources()
            target = staged / Path(*module.split('.')).with_suffix('.lean')
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            need(streamed_sha(target) == row['source_sha256'], 'exact staged source bytes')
            copied.append({'module': module, 'source': str(target), 'sha256': row['source_sha256']})
    for payload in lock['payloads']:
        need(streamed_sha(NETWORK / payload['network_relative_source']) == payload['source_sha256'],
             'same source-bound C payload')
    profiles = {'exact': {'RamanujanPV.DemandCriticalPair.Check0000': 96,
                'RamanujanPV.DemandCriticalPair.Check0250': 96,
                'RamanujanPV.DemandCriticalPair.GapCheck': 192,
                'RamanujanPV.PackedSievePrimitiveMaskMillion': 192,
                'RamanujanPV.FiniteLogSource': 96, 'RamanujanPV.FiniteCellSource': 96,
                'RamanujanPV.SelectedReplayAudit': 96}, 'prefix': {}}
    atomic(out / 'MEMORY_PROFILES.json', profiles)
    atomic(out / 'PREPARED.json', {'status': 'LOCKED_SOURCE_BYTES_PREPARED_NOT_LEAN_ACCEPTANCE',
           'source_lock_sha256': streamed_sha(lock_path), 'modules': expected_count,
           'script_sha256': frontend_sha, 'helper_sha256': sha(backend),
           'prepared_source_reused': args.prepared_root is not None,
           'old_application_objects_used': False, 'staged_sources': copied,
           'incidental_old_raw_data_modules': lock['old_raw_data_imports'],
           'old_local_primality_proof_modules': lock['old_local_primality_proof_modules'],
           'initial_resources': initial, 'commands': commands})
    if args.plan_only:
        print(json.dumps({'status': 'LOCKED_SOURCE_BYTES_ONLY_NOT_PROOF_ACCEPTANCE', 'modules': expected_count}))
        return
    resources()
    arguments = ['--context', args.context.resolve(), '--out', out / 'build', '--root', lock['root'],
                 '--application-source-root', staged, '--jobs', args.jobs, '--cpus', args.cpus,
                 '--memory-gib', 48, '--aggregate-gib', 300, '--host-reserve-gib', 512,
                 '--profile-json', out / 'MEMORY_PROFILES.json', '--owned-scratch-root', scratch]
    for theorem in lock['theorems']:
        arguments += ['--theorem', theorem]
    run(backend, arguments, proof=True)
    run(backend, ['--check', out / 'build'])
    build = strict_json(out / 'build/RESULT.json')
    need(build['status'] == 'FRESH_SELECTED_SOURCE_CLOSURE_PASS' and
         build['old_application_objects_used'] is False and len(build['records']) == expected_count + 1,
         'entire freshly compiled selected application closure')
    need(sha(Path(__file__)) == frontend_sha, 'frontend source stayed unchanged during execution')
    atomic(out / 'RESULT.json', {'status': 'COMPLETE_CLEAN_PACKED_MILLION_SOURCE_REPLAY',
           'modules': expected_count, 'source_lock_sha256': streamed_sha(lock_path),
           'build_result_sha256': streamed_sha(out / 'build/RESULT.json'),
           'helper_sha256': sha(backend), 'prepared_source_reused': args.prepared_root is not None,
           'old_application_objects_used': False, 'seconds': time.monotonic() - started,
           'commands': commands, 'script_sha256': frontend_sha})
    print(json.dumps({'status': 'COMPLETE_CLEAN_PACKED_MILLION_SOURCE_REPLAY', 'modules': expected_count}))


if __name__ == '__main__':
    main()
