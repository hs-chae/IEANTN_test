"""Additively validate an interrupted v2 continuation's successful new modules.

The original and v1 phases retain their actual commands and origins. A v2
failure, live process, or unreceipted object never becomes a successful proof.
"""
from pathlib import Path
import os
from reproduce_dual import need, sha, load
import resume_fft_dag_source_cold as original
import fft_dag_nested_lineage as prior

V2_SHA = '7745a37ec561b7e70f0bb971576dc62b85e054932d46a2c6b840f6a253661350'
V2_HELPER_SHA = 'f3fe25c8a8e89ab6e6a15c7ebf07bd210d24f9d899840b123335b6a87e4cd50a'


def validate_nested_lineage(prefix, candidate, context_path, c, continuations,
                            nested_continuation):
    need(sha(Path(prior.__file__)) == V2_HELPER_SHA, 'Frozen v2 helper changed')
    state = prior.validate_nested_lineage(prefix, candidate, context_path, c, continuations)
    directory = nested_continuation.resolve()
    need(directory != prefix and directory not in {Path(x['path']) for x in state['continuation_plans']},
         'Duplicate nested continuation')
    plan = load(directory / 'PLAN.json')
    need(plan['status'] == 'FROZEN_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV'
         and plan['nested_schema'] == 2, 'Only exact frozen v2 nested continuation supported')
    need(plan['controller_sha256'] == V2_SHA == sha(directory / 'resume_driver.executed.py'),
         'Frozen v2 actual controller differs')
    need(plan['continuation_helper_sha256'] == V2_HELPER_SHA
         and plan['continuation_plans'] == state['continuation_plans'],
         'V2 inherited lineage differs')
    need(plan['original_prefix'] == str(prefix)
         and plan['original_plan_sha256'] == sha(prefix / 'PLAN.json')
         == sha(directory / 'ORIGINAL_SOURCE_COLD_PLAN.json'),
         'V2 original experiment differs')
    need(plan['original_controller_sha256'] == original.ORIGINAL_DRIVER_SHA
         == sha(directory / 'driver.executed.py'), 'Original driver lineage differs')
    need(plan['context_helper_sha256'] == original.CONTEXT_HELPER_SHA
         and plan['context_sha256'] == sha(context_path)
         and plan['compiler_sha256'] == c['compiler_sha256']
         and plan['generic_dependencies'] == c['generic_dependencies'],
         'V2 exact compiler/context differs')
    need(plan['candidate_plan_sha256'] == sha(candidate / 'PLAN.json')
         and plan['proposal'] == state['proposal']
         and plan['sources'] == state['plan']['sources']
         and plan['payloads'] == state['proposal']['payloads'],
         'V2 source/data/mathematical parameters differ')
    need(plan['source_cold'] is False and plan['source_cold_lineage_resume'] is True
         and plan['outside_application_object_cache_used'] is False,
         'V2 provenance misclassified or external objects used')
    inherited = dict(state['successful'])
    need(plan['successful_prefix_modules'] == len(inherited)
         and plan['fresh_modules_required'] == len(state['rows']) - len(inherited)
         and set(plan['routes']) == set(inherited), 'V2 prefix/fresh universe differs')
    for name, row in state['rows'].items():
        need(sha(directory / 'sources' / row['file']) == row['sha256'],
             'V2 frozen source changed: ' + name)
    for row in state['proposal']['payloads']:
        q = directory / 'sources' / row['file']
        need(q.stat().st_size == row['bytes'] and sha(q) == row['sha256'],
             'V2 literal changed: ' + row['file'])
    for name, record in inherited.items():
        origin = state['origins'][name]; logical = state['logical_origins'][name]
        expected = dict(kind='REUSED_VERIFIED_SOURCE_COLD_LINEAGE_PREFIX',
                        compile_origin=str(origin), logical_compile_origin=str(logical),
                        phase=state['phases'][name],
                        receipt_sha256=sha(origin / (name + '.COMPILED.json')),
                        object_sha256=record['object_sha256'])
        need(plan['routes'][name] == expected, 'V2 inherited route changed: ' + name)
        need(load(directory / (name + '.COMPILED.json')) == record,
             'V2 inherited actual receipt changed: ' + name)
        old = origin / 'objects' / (name.replace('.', '/') + '.olean')
        obj = directory / 'objects' / (name.replace('.', '/') + '.olean')
        if not (os.stat(old).st_ino == os.stat(obj).st_ino
                and os.stat(old).st_dev == os.stat(obj).st_dev):
            need(sha(obj) == record['object_sha256'], 'V2 inherited object changed')
        for ext in ['stdout', 'stderr', 'time']:
            need(sha(directory / (name + '.' + ext)) == record[ext + '_sha256'],
                 'V2 inherited log changed')
    added = []; logical_run = None; skipped = []
    for path in sorted(directory.glob('*.COMPILED.json')):
        name = path.name.removesuffix('.COMPILED.json')
        need(name in state['rows'], 'Unknown v2 compiler receipt')
        if name in inherited:
            continue
        raw = load(path)
        if raw.get('returncode') != 0:
            skipped.append(dict(continuation=str(directory), module=name,
                                returncode=raw.get('returncode'),
                                reason='NO_SUCCESSFUL_V2_RECEIPT_NOT_REUSED'))
            continue
        command = raw['command']
        need(len(command) == 7 and command[2] == '-R', 'Invalid v2 compiler command')
        here = Path(command[3]); need(here.is_absolute() and here.name == 'sources',
                                    'Invalid v2 recorded source root')
        here = here.parent
        if logical_run is None:
            logical_run = here
        need(here == logical_run, 'Mixed actual v2 compile directories')
        record = original.receipt(directory, here, state['rows'][name], c['compiler'], True)
        expected = ['/usr/bin/time', '-v', '-o', str(here / (name + '.time')),
                    'prlimit', '--as=' + str(plan['per_compiler_AS_bytes']),
                    '--stack=' + str(256 * 2**20), '--',
                    *original.lean_command(c['compiler'], here, state['rows'][name])]
        need(record['resource_command'] == expected, 'Actual v2 initial resource command differs')
        state['successful'][name] = record; state['origins'][name] = directory
        state['logical_origins'][name] = here
        state['phases'][name] = 'VALIDATED_NESTED_CONTINUATION_2'; added.append(name)
    # An interrupted v2 run may have stopped before its first fresh receipt.
    # Record that zero phase honestly; production gates separately require the
    # actual 35 newly successful v2 modules before accepting a 1031+2 result.
    for name in state['successful']:
        need(all(dep.split('.')[0] in original.GENERIC or dep in state['successful']
                 for dep in state['rows'][name]['imports']),
             'V3 combined prefix lacks verified dependency: ' + name)
    state['continuation_plans'].append(dict(
        path=str(directory), plan_sha256=sha(directory / 'PLAN.json'),
        controller_sha256=V2_SHA, logical_run=str(logical_run), added_modules=added,
        original_result_present=(directory / 'RESULT.json').is_file(),
        old_outcome_unchanged=True, prior_nested_schema=2))
    state['skipped_continuation_receipts'].extend(skipped)
    state['continuation_successful_count'] = len(state['successful']) - state['original_successful_count']
    state['phase_counts'] = {phase: sum(p == phase for p in state['phases'].values())
                             for phase in sorted(set(state['phases'].values()))}
    return state
