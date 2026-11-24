#!/usr/bin/env python3
"""One source-only, physical-RAM-aware regeneration/proof composition.

The original conservative recipe remains unchanged. Its prepare-only route
regenerates the original numerical data. This additive route compiles the full
numerical/source-model consumer once, including the independent bounded grammar.
--smoke proves only pi(1000)=168 and the parameterized original high-main model;
it never claims to have discharged the fixed high-output count parameter.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
sys.path.insert(0, str(PARENT/'cold-foundation'))
import data_stage as D
import source_basis as B
need, sha, read, save, exact, rel = D.need, D.sha, D.read, D.save, D.exact, D.rel


def import_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sources():
    manifest = read(HERE/'SOURCE_CLOSURE.json')
    names = set()
    for row in manifest['modules']:
        need(row['module'] not in names, 'unique source-model compiler identity')
        names.add(row['module'])
        path = HERE/'source'/row['relative']
        need(row['relative'] == str(rel(row['module'])) and path.is_file() and
             not path.is_symlink() and sha(path) == row['sha256'],
             'exact unchanged accepted source-model/grammar capture')
    for row in manifest['resources']:
        need(sha(HERE/'source'/row['relative']) == row['sha256'], 'exact actual C source capture')
    return manifest


def compiler_engine(out):
    engine = HERE/'scripts/reproduce_physical_closure.py'
    parser = PARENT/'portable/scripts/rebuild_qrh_closure.py'
    freeze = read(HERE/'scripts/ENGINE_SOURCE_FREEZE.json')
    expected = {Path(row['path']).name: row['sha256'] for row in freeze['rows']}
    need(sha(engine) == expected[engine.name], 'reviewed physical-only replay engine')
    old = read(PARENT/'portable/CONTROLLERS.json')
    parser_sha = next(q['sha256'] for q in old['controllers']
                      if Path(q['path']).name == parser.name)
    need(sha(parser) == parser_sha, 'unchanged original Lean import parser')
    target = out/'engine/Solutions/Replay/scripts'
    target.mkdir(parents=True)
    shutil.copyfile(engine, target/engine.name)
    shutil.copyfile(parser, target/parser.name)
    return target/engine.name


def stage(out, name, command):
    start = time.monotonic()
    with (out/(name+'.stdout')).open('w') as stdout, (out/(name+'.stderr')).open('w') as stderr:
        cp = subprocess.run(['/usr/bin/time', '-v', '-o', str(out/(name+'.resources')),
                             *command], stdout=stdout, stderr=stderr,
                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    result = dict(command=command, returncode=cp.returncode, seconds=time.monotonic()-start,
         stdout_sha256=sha(out/(name+'.stdout')), stderr_sha256=sha(out/(name+'.stderr')),
         resources_sha256=sha(out/(name+'.resources')))
    save(out/(name+'.json'), result)
    need(cp.returncode == 0, 'actual source-only workflow stage failed:'+name)
    return result


def preparation_environment(out):
    """Reuse the original preparer unchanged, with an approved resource gate."""
    base = PARENT/'portable'
    target = out/'preparation/count-feasibility'
    paths = ['reproduce.py', 'SOURCE_CLOSURE.json', 'CONTROLLERS.json']
    captured = read(base/'SOURCE_CLOSURE.json')
    paths += ['source/'+row['relative'] for row in captured['modules']]
    paths += ['source/'+row['relative'] for row in captured['resources']]
    paths += [row['path'] for row in read(base/'CONTROLLERS.json')['controllers']]
    rows = []
    for name in paths:
        source = base/name
        destination = target/'portable'/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        rows.append(dict(path=str(destination.relative_to(out)), sha256=sha(source)))
    for name in ['recover_count.py', 'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json']:
        destination = target/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(PARENT/name, destination)
        rows.append(dict(path=str(destination.relative_to(out)), sha256=sha(PARENT/name)))
    variant = read(PARENT/'GENERATOR_RESOURCE_VARIANT.json')
    source = HERE/'scripts/generate_demand_certificate_resources.py'
    original = PARENT/'regeneration/generate_demand_certificate_resources.py'
    need(sha(source) == variant['safe_generator_sha256'] and
         sha(original) == variant['original_generator_sha256'] and
         source.read_bytes().replace(variant['exact_added_line'].encode(),
                                    variant['exact_removed_line'].encode()) == original.read_bytes(),
         'exact approved single resource gate change, all numerical algorithms unchanged')
    destination = target/'regeneration/generate_demand_certificate_resources.py'
    shutil.copyfile(source, destination)
    rows.append(dict(path=str(destination.relative_to(out)), sha256=sha(source)))
    metadata = read(PARENT/'REGENERATION.json')
    metadata['generator_sha256'] = variant['safe_generator_sha256']
    save(target/'REGENERATION.json', metadata)
    rows.append(dict(path=str((target/'REGENERATION.json').relative_to(out)),
                     sha256=sha(target/'REGENERATION.json')))
    save(out/'PREPARATION_ENVIRONMENT.json', dict(files=rows,
         resource_only_variant_sha256=sha(source), original_generator_sha256=sha(original),
         original_preparer_sha256=sha(base/'reproduce.py'),
         source_algorithm_unchanged=True, current_RAM_truthfully_checked=True))
    return target/'portable/reproduce.py'


def prepare(out, context, cpus, jobs, smoke):
    manifest = sources()
    need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(D.ROOT),
         'fresh experiment-owned clean output outside source checkout')
    out.mkdir()
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    engine = compiler_engine(out)
    old = preparation_environment(out)
    command = [sys.executable, str(old), '--context', str(context), '--out', str(out/'base'),
               '--cpus', cpus, '--jobs', str(jobs), '--prepare-only']
    if smoke:
        command += ['--smoke']
    generation = stage(out, 'regenerate', command)
    source = out/'base/source'
    collisions = []
    for row in manifest['modules']:
        target = source/row['relative']
        original = HERE/'source'/row['relative']
        if target.exists():
            need(sha(target) == row['sha256'], 'exact same-source namespace collision')
            collisions.append(row['module'])
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, target)
    for row in manifest['resources']:
        target = source/row['relative']
        if target.exists():
            need(sha(target) == row['sha256'], 'same actual included C source')
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(HERE/'source'/row['relative'], target)
    proposal = read(out/'base/proposal/PROPOSAL.json')
    chunks = (proposal['records']+32767)//32768
    namespace = 'RamanujanPV.PureCountWorkflowControl' if smoke else D.NS
    value = [1000, 168] if smoke else [1490000000000, 55206486339]
    if smoke:
        roots = ['RecoveredCountConsumer', 'SourceOutputAdapter', 'CounterSyntaxAudit']
        profiles = dict(exact={}, prefix={})
        per_task, default = 48, 48
    else:
        roots = ['CountSourceFinal', 'CountSourceAudit', 'CounterSyntaxAudit',
                 'RecoveredCountConsumer']
        profiles = read(HERE/'FULL_NUMERICAL_PROFILES.json')
        profiles['exact'].update({D.NS+'.Final': 256, 'CountSourceAudit': 256,
                                  'CounterSyntaxAudit': 256, 'CountSourceFinal': 256})
        profiles['exact'].update({D.NS+'.Check'+format(i, '04d'): 128
                                  for i in range(chunks)})
        per_task, default = 300, 64
    save(out/'PROFILES.json', profiles)
    symbols = [namespace+'.part_'+format(i, '04d') for i in range(chunks)]
    symbols += [namespace+'.'+name for name in ['gaps_checked', 'entries_checked',
                                               'root_'+str(value[0]), 'pi_'+str(value[0])]]
    symbols += ['RHOcticPush.RecoveredCount.'+name for name in
                ['count', 'actual_C_model_execution', 'exact_source_bytes_and_execution']]
    symbols += ['RHOcticPush.SourceOutputAdapter.canonical_source_output',
                'RHOcticPush.SourceOutputAdapter.every_source_output']
    if not smoke:
        symbols += ['RHOcticPush.ColdCount.'+name for name in
             ['count', 'complete_actual_source_run', 'every_actual_source_output',
              'all_finished_pi', 'all_finished_source_function']]
    command = [sys.executable, str(engine), '--context', str(context), '--out', str(out/'replay'),
        '--application-source-root', str(source), '--jobs', str(jobs), '--cpus', cpus,
        '--memory-gib', str(default), '--profile-json', str(out/'PROFILES.json'),
        '--address-ceiling-gib', str(per_task), '--host-reserve-gib', '512']
    for name in roots:
        command += ['--root', name]
    for name in symbols:
        command += ['--theorem', name]
    modules = [dict(module='.'.join(p.relative_to(source).with_suffix('').parts),
                    source_sha256=sha(p)) for p in sorted(source.rglob('*.lean'))]
    plan = dict(schema='RH_PORTABLE_SOURCE_RUN_V1', wrapper_sha256=sha(__file__),
        source_capture_sha256=sha(HERE/'SOURCE_CLOSURE.json'), engine_sha256=sha(engine),
        engine_freeze_sha256=sha(HERE/'scripts/ENGINE_SOURCE_FREEZE.json'),
        original_prepare_wrapper_sha256=sha(old), original_sources_sha256=sha(out/'base/SOURCES.json'),
        preparation_environment_sha256=sha(out/'PREPARATION_ENVIRONMENT.json'),
        context=str(context), context_sha256=sha(context), generation=generation,
        python_executable=sys.executable, python_executable_sha256=sha(Path(sys.executable).resolve()),
        source_root=str(source), sources=modules, actual_C_resources=manifest['resources'],
        exact_source_collisions=collisions, smoke=smoke, namespace=namespace,
        mathematical_target=value, arithmetic_chunks=chunks, roots=roots, selected_theorems=symbols,
        command=command, profiles_sha256=sha(out/'PROFILES.json'), jobs=jobs, cpus=cpus,
        physical_native_association_proved=False,
        scope='SMOKE pi1000 and parameterized fixed high-main model, not fixed high-output proof'
              if smoke else 'Full regenerated count and actual independent-source/model consumer')
    save(out/'PLAN.json', plan)
    return plan


def verify(out):
    # The complete outer source/path/dependency reader is implemented separately
    # from the mathematical execution engine and called by the actual CLI.
    import readback
    return readback.verify(out)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--context', type=Path)
    parser.add_argument('--check', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--cpus', default=','.join(map(str, range(64, 86))))
    parser.add_argument('--jobs', type=int, default=22)
    args = parser.parse_args()
    if args.check:
        need(args.out is None and args.context is None and not args.prepare_only and not args.smoke,
             'readback route arguments')
        print(verify(args.check.resolve())['status'])
        return
    need(args.out is not None and args.context is not None, 'explicit clean context/output')
    need(type(args.jobs) is int and 1 <= args.jobs <= 22, 'bounded physical-aware CPU lanes')
    cpus = list(map(int, args.cpus.split(',')))
    need(len(cpus) == len(set(cpus)) and len(cpus) >= args.jobs and
         set(cpus) <= os.sched_getaffinity(0), 'actual distinct CPU affinities')
    out = args.out.resolve()
    plan = prepare(out, args.context.resolve(), args.cpus, args.jobs, args.smoke)
    if args.prepare_only:
        print('PREPARED_PHYSICAL_SOURCE_RUN_NO_PROOF_COMPILERS')
        return
    stage(out, 'compile_all', plan['command'])
    import readback
    result = readback.verify(out, write_probes=True, candidate=True)
    save(out/'RESULT.json', result)
    verify(out)
    print(result['status'])


if __name__ == '__main__':
    main()
