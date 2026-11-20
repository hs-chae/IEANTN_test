#!/usr/bin/env python3
"""Regenerate exact combined sources, then optionally rebuild all 554 apps.

Source preparation and a checked plan are not mathematical acceptance. The
unchanged guarded backend alone accepts a complete fresh proof execution.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from reproduce_guarded_coupled_closure import strict_json, need, sha

S = Path(__file__).resolve().parents[1]
NETWORK = S.parents[1]
LOCK = S / 'evidence/prime-base-combined-clean-v1/SOURCE_LOCK.json'
LOCK_SHA = '55d3856aca4e5e493feec9fb562a2d2bda74ffc5f008819af893a4150845932e'
PYTHON = [sys.executable] + (['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else [])


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.pending')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def digest(path):
    import hashlib
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            value.update(block)
    return value.hexdigest()


def locked():
    need(sha(LOCK) == LOCK_SHA, 'frozen combined source lock identity')
    lock = strict_json(LOCK)
    need(lock['source_module_count'] == len(lock['modules']) == 554, 'exact 554 application sources')
    need(len({r['module'] for r in lock['modules']}) == 554, 'distinct exact source identities')
    need(lock['roots'] == ['RamanujanPV.PrimeBaseCombinedIndependentAudit'], 'fixed combined audit root')
    need(lock['theorems'] == ['RamanujanPV.PrimeBaseCombinedResult.actual_source_bindings',
         'RamanujanPV.PrimeBaseCombinedResult.source_linked_uniform_gap',
         'RamanujanPV.PrimeBaseCombinedResult.source_linked_real_interval'], 'exact source-linked conclusions')
    for name, expected in lock['script_pins'].items():
        need(sha(S / 'scripts' / name) == expected, 'unchanged dependency script ' + name)
    need(digest(S / 'evidence/packed-numerical-source-v1/BOUND_SOURCE_LOCK.json') ==
         lock['original_bound_lock_sha256'], 'unchanged original source lock')
    return lock


def verify(directory, completed):
    lock = locked()
    receipt_name = 'RESULT.json' if completed else 'PREPARED.json'
    result = strict_json(directory / receipt_name)
    need(result['status'] == ('COMPLETE_FRESH_COMBINED_SOURCE_REPLAY' if completed else
         'EXACT_COMBINED_SOURCES_PREPARED_NOT_PROOF_ACCEPTANCE'), 'exact receipt scope')
    need(result['source_lock_sha256'] == sha(LOCK), 'exact combined lock')
    need(result['frontend_sha256'] == sha(Path(__file__)) == sha(directory / 'frontend.py'),
         'current and actually executed frontend identity')
    need(result['context_sha256'] == sha(result['context']), 'exact context receipt')
    need(result['old_application_objects_used'] is False, 'no old application objects')
    expected = {row['module']: row['source_sha256'] for row in lock['modules']}
    records = result['sources']
    need(len(records) == 554 and {r['module']: r['sha256'] for r in records} == expected,
         'complete exact planned source population')
    for row in records:
        path = Path(row['source']).resolve()
        need(path == (directory / 'source' / Path(*row['module'].split('.')).with_suffix('.lean')).resolve()
             if row['staged'] else path.is_relative_to(NETWORK), 'exact staged or tracked source provenance')
        need(digest(path) == row['sha256'], 'current source bytes ' + row['module'])
    need(result['script_pins'] == lock['script_pins'], 'entire exact child script identity population')
    need(type(result['jobs']) is int and 1 <= result['jobs'] <= 8, 'actual bounded preparation concurrency')
    cpus = result['cpus']
    need(type(cpus) is str and cpus and all(v.isdecimal() for v in cpus.split(',')), 'recorded CPU arguments')
    original_arguments = ['--context', result['context'], '--out', str(directory / 'original-sources'),
                          '--bound-result', '--plan-only', '--jobs', str(result['jobs']), '--cpus', cpus]
    if result['source_preparation_reused']:
        original_arguments += ['--prepared-root', result['prepared_root']]
    else:
        need(result['prepared_root'] is None, 'default preparation does not reuse prior sources')
    expected_commands = [('reproduce_packed_million.py', original_arguments),
        ('generate_prime_base_mask_scout.py', ['--out', str(directory / 'prime-base')]),
        ('generate_balanced_mask_data.py', ['--baseline-source', str(S / 'evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean'),
          '--out', str(directory / 'balanced-data'), '--data-only-4096', '--provider-check'])]
    backend_arguments = ['--context', result['context'], '--out', str(directory / 'build'),
        '--application-source-root', str(directory / 'source'), '--jobs', str(result['jobs']), '--cpus', cpus,
        '--memory-gib', '48', '--aggregate-gib', '300', '--host-reserve-gib', '512',
        '--profile-json', str(directory / 'MEMORY_PROFILES.json'), '--owned-scratch-root',
        str(Path(strict_json(result['context'])['new_application_object_root']).resolve().parent)]
    for root in lock['roots']:
        backend_arguments += ['--root', root]
    for theorem in lock['theorems']:
        backend_arguments += ['--theorem', theorem]
    if completed:
        expected_commands += [('reproduce_guarded_coupled_closure.py', backend_arguments),
                              ('reproduce_guarded_coupled_closure.py', ['--check', str(directory / 'build')])]
    need(len(result['commands']) == len(expected_commands), 'complete actual child-command ledger')
    for index, (command, expected) in enumerate(zip(result['commands'], expected_commands)):
        call = command['command']
        skip = 2 if len(call) > 1 and call[1] in ['-O', '-OO'] else 1
        need(call[skip:] == [str(S / 'scripts' / expected[0]), *expected[1]],
             'exact actual child workflow arguments')
        need(command['stdout'] == ('command-%02d.stdout' % index) and
             command['stderr'] == ('command-%02d.stderr' % index), 'exact command log roles')
        need(command['exit_code'] == 0, 'every actual source-generation child succeeded')
        need(digest(directory / command['stdout']) == command['stdout_sha256'] and
             digest(directory / command['stderr']) == command['stderr_sha256'], 'actual command logs')
    plan = strict_json(directory / 'COMBINED_PLAN.json')
    need(plan['roots'] == lock['roots'] and plan['theorems'] == lock['theorems'] and
         plan['source_lock_sha256'] == sha(LOCK) and plan['source_module_count'] == 554,
         'exact future mathematical workload')
    future = plan['backend_command']
    skip = 2 if len(future) > 1 and future[1] in ['-O', '-OO'] else 1
    need(future[skip:] == [str(S / 'scripts/reproduce_guarded_coupled_closure.py'), *backend_arguments],
         'exact executable future backend workload')
    for payload in lock['payloads']:
        need(digest(NETWORK / payload['network_relative_source']) == payload['source_sha256'],
             'exact source-bound C payload')
    if completed:
        backend_plan = strict_json(directory / 'build/PLAN.json')
        need(backend_plan['targets'] == lock['roots'] and backend_plan['selected_theorems'] == lock['theorems'],
             'actual completed combined roots')
        need({r['module']: r['source_sha256'] for r in backend_plan['modules']} == expected and
             len(backend_plan['modules']) == 554, 'actual completed module census')
        need(digest(directory / 'build/RESULT.json') == result['build_result_sha256'], 'actual proof result hash')
        need(subprocess.call([*PYTHON, str(S / 'scripts/reproduce_guarded_coupled_closure.py'),
             '--check', str(directory / 'build')]) == 0, 'actual full backend readback')
    return {'status': 'CHECKED_COMPLETE_FRESH_COMBINED_SOURCE_REPLAY' if completed else
            'CHECKED_EXACT_COMBINED_SOURCE_PLAN_NOT_PROOF_ACCEPTANCE', 'modules': 554,
            'full_fresh_proof_execution_checked': completed}


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--prepared-root', type=Path,
                        help='Optional exact regenerated original-source root; no proof objects are reused')
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--cpus', default='84,85,86,87,88,89')
    parser.add_argument('--plan-only', action='store_true')
    parser.add_argument('--check-plan', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    need(not (args.check_plan and args.check), 'separate check modes')
    if args.check_plan or args.check:
        need(args.out is None and args.prepared_root is None and not args.plan_only, 'read-only check mode')
        print(json.dumps(verify((args.check or args.check_plan).resolve(), bool(args.check))))
        return
    lock = locked()
    need(args.out is not None, 'fresh output required')
    context = strict_json(args.context)
    owned = Path(context['new_application_object_root']).resolve().parent
    out = args.out.resolve()
    need(out.is_relative_to(owned) and out != owned and not out.exists() and out.parent.is_dir(),
         'fresh experiment-owned output')
    cpus = [int(v) for v in args.cpus.split(',')]
    need(len(cpus) == len(set(cpus)) and set(cpus) <= os.sched_getaffinity(0), 'actual distinct CPUs')
    need(1 <= args.jobs <= len(cpus) <= 8, 'bounded concurrency')
    need(sha(context['compiler']) == context['compiler_sha256'] == lock['compiler_sha256'], 'pinned compiler')
    out.mkdir()
    (out / 'frontend.py').write_bytes(Path(__file__).read_bytes())
    commands = []
    start = time.monotonic()
    stopped = []
    for number in [signal.SIGUSR1, signal.SIGTERM, signal.SIGINT]:
        signal.signal(number, lambda value, _frame: stopped.append(value))

    def checkpoint():
        if stopped:
            atomic(out / 'CHECKPOINT.json', {'status': 'DRAINED_NOT_PROOF_ACCEPTANCE',
                                           'signals': stopped, 'commands': commands})
            raise SystemExit(3)

    def run(script, arguments):
        checkpoint()
        index = len(commands)
        stdout = out / ('command-%02d.stdout' % index)
        stderr = out / ('command-%02d.stderr' % index)
        command = [*PYTHON, str(script), *map(str, arguments)]
        with stdout.open('w') as so, stderr.open('w') as se:
            child = subprocess.Popen(command, stdout=so, stderr=se,
                                     preexec_fn=lambda: os.sched_setaffinity(0, set(cpus)))
            forwarded = False
            while child.poll() is None:
                if stopped and not forwarded:
                    # Finish source preparation's current child. Send the
                    # proof controller a drain only after its actual state
                    # file confirms that its scheduler is initialized.
                    if script.name == 'reproduce_guarded_coupled_closure.py' and (out / 'build/RUN_STATE.json').exists():
                        child.send_signal(signal.SIGUSR1)
                        forwarded = True
                time.sleep(0.1)
            code = child.returncode
        commands.append({'command': command, 'exit_code': code, 'stdout': stdout.name,
                         'stderr': stderr.name, 'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr)})
        atomic(out / 'COMMANDS.json', commands)
        checkpoint()
        need(code == 0, 'actual child completion ' + script.name)

    baseline_args = ['--context', args.context.resolve(), '--out', out / 'original-sources',
                     '--bound-result', '--plan-only', '--jobs', args.jobs, '--cpus', args.cpus]
    if args.prepared_root:
        baseline_args += ['--prepared-root', args.prepared_root.resolve()]
    run(S / 'scripts/reproduce_packed_million.py', baseline_args)
    original = strict_json(out / 'original-sources/PREPARED.json')
    need(original['modules'] == 549 and original['old_application_objects_used'] is False,
         'actual original exact source preparation; no old objects')
    run(S / 'scripts/generate_prime_base_mask_scout.py', ['--out', out / 'prime-base'])
    run(S / 'scripts/generate_balanced_mask_data.py', ['--baseline-source',
        S / 'evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean',
        '--out', out / 'balanced-data', '--data-only-4096', '--provider-check'])
    generated = {}
    for proposal_path, list_name in [(out / 'prime-base/PROPOSAL.json', 'modules'),
                                     (out / 'balanced-data/PROPOSAL.json', 'records')]:
        for row in strict_json(proposal_path)[list_name]:
            generated[row['module']] = Path(row['source'])
    source_root = out / 'source'
    source_root.mkdir()
    sources = []
    for row in lock['modules']:
        module = row['module']
        relative = Path(*module.split('.')).with_suffix('.lean')
        if row['kind'] == 'tracked':
            source = (NETWORK / row['network_relative_source']).resolve()
            need(source.is_relative_to(NETWORK), 'tracked source in network')
            staged = False
        else:
            source = generated.get(module, out / 'original-sources/source' / relative)
            need(source.resolve().is_relative_to(out), 'generated source owned by current preparation')
            target = source_root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            need(digest(source) == row['source_sha256'], 'exact generated source ' + module)
            shutil.copyfile(source, target)
            source, staged = target, True
        need(digest(source) == row['source_sha256'], 'all locked scientific source bytes ' + module)
        sources.append({'module': module, 'source': str(source), 'sha256': row['source_sha256'], 'staged': staged})
    profile = strict_json(out / 'original-sources/MEMORY_PROFILES.json')
    # The combined evaluator is measured below48GiB, but its source-only DATA
    # and numerical proof are independently capped96GiB for cold replay.
    profile['exact']['RamanujanPV.PrimeBaseMaskScout.CombinedP'] = 96
    profile['exact']['RamanujanPV.PrimeBaseCombinedIndependentAudit'] = 96
    atomic(out / 'MEMORY_PROFILES.json', profile)
    arguments = ['--context', args.context.resolve(), '--out', out / 'build',
                 '--application-source-root', source_root, '--jobs', args.jobs, '--cpus', args.cpus,
                 '--memory-gib', 48, '--aggregate-gib', 300, '--host-reserve-gib', 512,
                 '--profile-json', out / 'MEMORY_PROFILES.json', '--owned-scratch-root', owned]
    for root in lock['roots']:
        arguments += ['--root', root]
    for theorem in lock['theorems']:
        arguments += ['--theorem', theorem]
    atomic(out / 'COMBINED_PLAN.json', {'status': 'LOCKED_FUTURE_PROOF_WORKLOAD_NOT_ACCEPTANCE',
           'roots': lock['roots'], 'theorems': lock['theorems'], 'source_module_count': 554,
           'source_lock_sha256': sha(LOCK), 'backend_command': [*PYTHON,
            str(S / 'scripts/reproduce_guarded_coupled_closure.py'), *map(str, arguments)]})
    prepared = {'status': 'EXACT_COMBINED_SOURCES_PREPARED_NOT_PROOF_ACCEPTANCE',
                'source_lock_sha256': sha(LOCK), 'frontend_sha256': sha(Path(__file__)),
                'context': str(args.context.resolve()), 'context_sha256': sha(args.context),
                'script_pins': lock['script_pins'], 'sources': sources, 'commands': list(commands),
                'source_preparation_reused': args.prepared_root is not None,
                'prepared_root': str(args.prepared_root.resolve()) if args.prepared_root else None,
                'jobs': args.jobs, 'cpus': args.cpus,
                'old_application_objects_used': False, 'full_fresh_proof_execution_checked': False,
                'seconds': time.monotonic() - start}
    atomic(out / 'PREPARED.json', prepared)
    verify(out, False)
    if args.plan_only:
        print(json.dumps({'status': prepared['status'], 'modules': 554}))
        return
    run(S / 'scripts/reproduce_guarded_coupled_closure.py', arguments)
    run(S / 'scripts/reproduce_guarded_coupled_closure.py', ['--check', out / 'build'])
    result = dict(prepared, status='COMPLETE_FRESH_COMBINED_SOURCE_REPLAY', commands=commands,
                  full_fresh_proof_execution_checked=True,
                  build_result_sha256=digest(out / 'build/RESULT.json'), seconds=time.monotonic() - start)
    atomic(out / 'RESULT.json', result)
    print(json.dumps(verify(out, True)))


if __name__ == '__main__':
    main()
