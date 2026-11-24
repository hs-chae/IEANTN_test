#!/usr/bin/env python3
"""Independent complete ownership/source/import reader for the portable route."""
from pathlib import Path
import importlib.util
import json
import math
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
sys.path.insert(0, str(PARENT/'cold-foundation'))
import data_stage as D
import source_basis as B
import remaining_stage as R
need, sha, read, save, exact, rel = D.need, D.sha, D.read, D.save, D.exact, D.rel


def load_engine(path):
    sys.path.insert(0, str(path.parent))
    spec = importlib.util.spec_from_file_location('portable_physical_reader', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sources_check(out, plan):
    source = out/'base/source'
    need(source.resolve() == source and plan['source_root'] == str(source),
         'exact owned source root')
    old = read(out/'base/SOURCES.json')
    proposal = read(out/'base/proposal/PROPOSAL.json')
    portable = load_portable()
    frozen, regeneration = portable.frozen()
    recovery = portable.import_recovery()
    smoke = plan['smoke']
    need(type(smoke) is bool, 'strict smoke/full distinction')
    namespace = 'RamanujanPV.PureCountWorkflowControl' if smoke else D.NS
    target = [1000, 168] if smoke else [1490000000000, 55206486339]
    need(exact(proposal['queries'], [target[0]]) and len(proposal['results']) == 1 and
         type(proposal['results'][0]['N']) is int and proposal['results'][0]['N'] == target[0] and
         type(proposal['results'][0]['value']) is int and
         proposal['results'][0]['value'] == target[1], 'exact regenerated query/result identity')
    chunks = (proposal['records']+32767)//32768
    need(exact(plan['mathematical_target'], target) and plan['namespace'] == namespace and
         type(plan['arithmetic_chunks']) is int and plan['arithmetic_chunks'] == chunks and
         sha(out/'base/proposal/PROPOSAL.json') == old['untrusted_proposal_sha256'],
         'actual regenerated exact numerical target')
    if not smoke:
        lock = read(PARENT/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json')
        need(proposal['packed_sha256'] == regeneration['original_packed_sha256'] and
             {q['module']: q['sha256'] for q in proposal['modules']} == lock['modules'],
             'all original numerical data identities exactly regenerated')
    expected = {q['module']: q['sha256'] for q in proposal['modules']}
    expected.update({q['module']: q['source_sha256'] for q in frozen['modules']})
    for index in range(chunks):
        text = recovery.leaf_text(format(index, '04d'), index*32768,
                                   min(32768, proposal['records']-index*32768))
        if smoke:
            text = text.replace('HighTransitionCount', 'PureCountWorkflowControl')
        expected[namespace+'.Check'+format(index, '04d')] = __import__('hashlib').sha256(text.encode()).hexdigest()
    text = recovery.closed_consumer()
    if smoke:
        text = text.replace('HighTransitionCount', 'PureCountWorkflowControl')\
            .replace('1490000000000', '1000').replace('55206486339', '168')
    expected['RecoveredCountConsumer'] = __import__('hashlib').sha256(text.encode()).hexdigest()
    need({q['module']: q['source_sha256'] for q in old['modules']} == expected and
         len(old['modules']) == len(expected), 'canonical complete original prepared source recipe')
    capture = read(HERE/'SOURCE_CLOSURE.json')
    collisions = []
    for row in capture['modules']:
        if row['module'] in expected:
            need(expected[row['module']] == row['sha256'], 'exact same-source module collision')
            collisions.append(row['module'])
        expected[row['module']] = row['sha256']
    need(exact(collisions, plan['exact_source_collisions']), 'all canonical source collision choices')
    need(len(plan['sources']) == len(expected) and
         {q['module']: q['source_sha256'] for q in plan['sources']} == expected,
         'complete source capture without replacement or omitted numerical parts')
    files = sorted(source.rglob('*.lean'))
    need({'.'.join(p.relative_to(source).with_suffix('').parts) for p in files} == set(expected),
         'no hidden or missing application source')
    for name, digest in expected.items():
        D.owned_file(str(source/rel(name)), source/rel(name), source, digest)
    for resource in capture['resources']:
        path = source/resource['relative']
        D.owned_file(str(path), path, source, resource['sha256'])
    return expected, capture, chunks, namespace, target


def load_portable():
    path = PARENT/'portable/reproduce.py'
    spec = importlib.util.spec_from_file_location('unchanged_original_portable', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def preparation_check(out, plan):
    need(sha(out/'PREPARATION_ENVIRONMENT.json') == plan['preparation_environment_sha256'],
         'exact resource-only preparation environment capture')
    environment = read(out/'PREPARATION_ENVIRONMENT.json')
    variant = read(PARENT/'GENERATOR_RESOURCE_VARIANT.json')
    need(environment['resource_only_variant_sha256'] == variant['safe_generator_sha256'] and
         environment['original_generator_sha256'] == variant['original_generator_sha256'] and
         environment['original_preparer_sha256'] == sha(PARENT/'portable/reproduce.py') and
         environment['source_algorithm_unchanged'] is True and
         environment['current_RAM_truthfully_checked'] is True,
         'approved proposer admission variant, never a changed numerical algorithm')
    for row in environment['files']:
        path = out/row['path']
        D.owned_file(str(path), path, out/'preparation', row['sha256'])
    target = out/'preparation/count-feasibility'
    need(sha(target/'portable/reproduce.py') == sha(PARENT/'portable/reproduce.py') and
         sha(target/'recover_count.py') == sha(PARENT/'recover_count.py') and
         sha(target/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json') ==
         sha(PARENT/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json'),
         'unchanged original preparation, pure-proof generator and source identity lock')
    metadata = read(PARENT/'REGENERATION.json')
    metadata['generator_sha256'] = variant['safe_generator_sha256']
    need(exact(read(target/'REGENERATION.json'), metadata),
         'only resource proposer identity changes in local preparation metadata')
    actual = target/'regeneration/generate_demand_certificate_resources.py'
    original = PARENT/'regeneration/generate_demand_certificate_resources.py'
    need(sha(actual) == variant['safe_generator_sha256'] and
         actual.read_bytes().replace(variant['exact_added_line'].encode(),
                                     variant['exact_removed_line'].encode()) == original.read_bytes(),
         'exact single resource-admission source difference')


def stage_check(out, name, expected_command):
    stage = read(out/(name+'.json'))
    need(exact(stage['command'], expected_command) and type(stage['returncode']) is int and
         stage['returncode'] == 0, 'exact successful actual top-level stage command:'+name)
    for suffix in ['stdout', 'stderr', 'resources']:
        path = out/(name+'.'+suffix)
        D.owned_file(str(path), path, out, stage[suffix+'_sha256'])
    D.observed_wall((out/(name+'.resources')).read_text(), stage['seconds'])
    return stage


def verify(out, write_probes=False, candidate=False):
    out = Path(out).resolve()
    plan = read(out/'PLAN.json')
    need(plan['schema'] == 'RH_PORTABLE_SOURCE_RUN_V1' and
         plan['wrapper_sha256'] == sha(HERE/'reproduce.py') == sha(out/'reproduce.executed.py') and
         plan['source_capture_sha256'] == sha(HERE/'SOURCE_CLOSURE.json') and
         plan['engine_freeze_sha256'] == sha(HERE/'scripts/ENGINE_SOURCE_FREEZE.json'),
         'exact executed portable/source/engine identity')
    engine_path = out/'engine/Solutions/Replay/scripts/reproduce_physical_closure.py'
    need(sha(engine_path) == plan['engine_sha256'] ==
         sha(HERE/'scripts/reproduce_physical_closure.py') and
         sha(PARENT/'portable/reproduce.py') == plan['original_prepare_wrapper_sha256'] and
         sha(out/'base/SOURCES.json') == plan['original_sources_sha256'],
         'same original preparation and resource-only executed engine')
    preparation_check(out, plan)
    expected, capture, chunks, namespace, target = sources_check(out, plan)
    need(type(plan['jobs']) is int and 1 <= plan['jobs'] <= 22 and
         type(plan['cpus']) is str, 'strict bounded portable worker/CPU metadata')
    need(type(plan['python_executable']) is str and
         sha(Path(plan['python_executable']).resolve()) == plan['python_executable_sha256'],
         'actual recorded preparation/engine Python binary')
    roots = ['RecoveredCountConsumer', 'SourceOutputAdapter', 'CounterSyntaxAudit'] \
            if plan['smoke'] else ['CountSourceFinal', 'CountSourceAudit', 'CounterSyntaxAudit',
                                  'RecoveredCountConsumer']
    symbols = [namespace+'.part_'+format(i, '04d') for i in range(chunks)]
    symbols += [namespace+'.'+name for name in ['gaps_checked', 'entries_checked',
                                               'root_'+str(target[0]), 'pi_'+str(target[0])]]
    symbols += ['RHOcticPush.RecoveredCount.'+name for name in
                ['count', 'actual_C_model_execution', 'exact_source_bytes_and_execution']]
    symbols += ['RHOcticPush.SourceOutputAdapter.canonical_source_output',
                'RHOcticPush.SourceOutputAdapter.every_source_output']
    if not plan['smoke']:
        symbols += ['RHOcticPush.ColdCount.'+name for name in
             ['count', 'complete_actual_source_run', 'every_actual_source_output',
              'all_finished_pi', 'all_finished_source_function']]
    need(exact(plan['roots'], roots) and exact(plan['selected_theorems'], symbols),
         'all exact source/model/count theorem roots, never a selected weaker branch')
    generation_command = [plan['python_executable'],
        str(out/'preparation/count-feasibility/portable/reproduce.py'),
        '--context', plan['context'], '--out', str(out/'base'), '--cpus', plan['cpus'],
        '--jobs', str(plan['jobs']), '--prepare-only']
    if plan['smoke']:
        generation_command += ['--smoke']
    generation = stage_check(out, 'regenerate', generation_command)
    need(exact(plan['generation'], generation), 'actual recorded preparation execution receipt')
    engine_command = [plan['python_executable'], str(engine_path), '--context', plan['context'],
        '--out', str(out/'replay'), '--application-source-root', str(out/'base/source'),
        '--jobs', str(plan['jobs']), '--cpus', plan['cpus'], '--memory-gib',
        '48' if plan['smoke'] else '64', '--profile-json', str(out/'PROFILES.json'),
        '--address-ceiling-gib', '48' if plan['smoke'] else '300', '--host-reserve-gib', '512']
    for name in roots:
        engine_command += ['--root', name]
    for name in symbols:
        engine_command += ['--theorem', name]
    need(exact(plan['command'], engine_command), 'canonical whole-source execution command')
    stage_check(out, 'compile_all', engine_command)
    context = read(plan['context'])
    need(sha(plan['context']) == plan['context_sha256'], 'pinned clean generic context')
    B.validate_generic(context)
    engine = load_engine(engine_path)
    engine.validate(out/'replay')
    actual, result = read(out/'replay/PLAN.json'), read(out/'replay/RESULT.json')
    source = out/'base/source'
    generic = context['generic_libraries']+[
        str(Path(context['compiler']).parent.parent/'lib/lean')]
    need(actual['compiler'] == context['compiler'] and
         actual['compiler_sha256'] == context['compiler_sha256'] and
         actual['context_sha256'] == plan['context_sha256'] and
         actual['context'] == plan['context'] and exact(actual['generic_libraries'], generic) and
         exact(actual['targets'], plan['roots']) and
         exact(actual['selected_theorems'], plan['selected_theorems']),
         'actual generic-only mathematical execution command')
    need(exact(read(out/'PROFILES.json'), actual['resource_profile']) and
         sha(out/'PROFILES.json') == plan['profiles_sha256'] and
         type(actual['max_parallel_workers']) is int and actual['max_parallel_workers'] == plan['jobs'] and
         actual['host_reserve_bytes'] == 512 << 30 and
         exact(actual['cpus'], sorted(map(int, plan['cpus'].split(',')))),
         'same exact physical resource policy and CPU lanes')
    C = D.controller()
    seen, visiting, order = set(), set(), []
    def visit(name):
        if name in seen:
            return
        if name not in expected:
            need(not name.startswith(('RamanujanPV.', 'LCMSourcePV.', 'RHOcticPush.')) and
                 any((Path(g)/rel(name).with_suffix('.olean')).is_file() for g in generic),
                 'only approved generic imports outside exact application source universe')
            return
        need(name not in visiting, 'acyclic exact application source closure')
        visiting.add(name)
        imports = C.imports((source/rel(name)).read_text())
        for imported in imports:
            visit(imported)
        visiting.remove(name)
        seen.add(name)
        order.append(dict(module=name, root=str(source), source=str(source/rel(name)),
             source_sha256=expected[name], imports=imports))
    for name in plan['roots']:
        visit(name)
    need([{k: row[k] for k in ['module', 'root', 'source', 'source_sha256', 'imports']}
         for row in actual['modules']] == order,
         'entire actual source dependency closure, not a source-reading heuristic')
    roots = plan['roots']
    selected = plan['selected_theorems']
    audit_text = ''.join('import '+name+'\n' for name in roots)+\
                 ''.join('#print axioms '+name+'\n' for name in selected)
    audit = out/'replay/source/RamanujanPV/SelectedReplayAudit.lean'
    need(audit.read_text() == audit_text, 'canonical complete selected theorem audit source')
    profiles = read(out/'PROFILES.json')
    wanted_profiles = dict(exact={}, prefix={}) if plan['smoke'] else read(
        HERE/'FULL_NUMERICAL_PROFILES.json')
    if not plan['smoke']:
        wanted_profiles['exact'].update({D.NS+'.Final': 256, 'CountSourceAudit': 256,
                                         'CounterSyntaxAudit': 256, 'CountSourceFinal': 256})
        wanted_profiles['exact'].update({D.NS+'.Check'+format(i, '04d'): 128
                                         for i in range(chunks)})
    need(exact(profiles, wanted_profiles), 'exact source-specific numerical address-space profiles')
    def memory(module):
        if module in profiles['exact']:
            return profiles['exact'][module] << 30
        matches = [(key, value) for key, value in profiles['prefix'].items()
                   if module == key or module.startswith(key+'.')]
        default = 48 if plan['smoke'] else 64
        return (max(matches, key=lambda item: len(item[0]))[1] if matches else default) << 30
    object_map, records = {}, result['records']
    need([q['module'] for q in records] == [q['module'] for q in order]+[
         'RamanujanPV.SelectedReplayAudit'], 'exact all-source execution record population')
    for row in records:
        module = row['module']
        root = out/'replay/source' if module == 'RamanujanPV.SelectedReplayAudit' else source
        path, obj = root/rel(module), out/'replay/lean'/rel(module).with_suffix('.olean')
        logs = out/'replay/audit'/module
        need(exact(row['command'], [context['compiler'], '-j1', '-R', str(root), str(path),
                                   '-o', str(obj)]), 'exact actual source/compiler/object command')
        for key, value in [('source', path), ('object', obj), ('stdout', logs/'stdout'),
                           ('stderr', logs/'stderr'), ('rusage', logs/'rusage')]:
            scope = source if key == 'source' and root == source else out/'replay'
            D.owned_file(row[key], value, scope, row[key+'_sha256'])
        need(type(row['exit_code']) is int and row['exit_code'] == 0 and
             row['source_unchanged_during_compile'] is True and
             type(row['memory_limit_bytes']) is int and row['memory_limit_bytes'] == memory(module) and
             row['oom_or_sigkill_event'] is False, 'actual source success and exact address-space cap')
        usage = (logs/'rusage').read_text()
        match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
        need(match is not None and type(row['peak_rss_bytes']) is int and
             row['peak_rss_bytes'] == int(match[1])*1024 and
             0 < row['peak_rss_bytes'] <= row['memory_limit_bytes'], 'actual child peak RAM')
        D.observed_wall(usage, row['seconds'])
        D.owned_file(str(logs/'source.lean'), logs/'source.lean', out/'replay', row['source_sha256'])
        output = (logs/'stdout').read_text()+(logs/'stderr').read_text()
        need(not any(word in output for word in
                     ['sorryAx', 'Lean.ofReduceBool', 'declaration uses `sorry`']),
             'no native execution axiom or admitted mathematical proof')
        object_map[obj.resolve()] = row['object_sha256']
    probes = []
    for row in records:
        module = row['module']
        root = out/'replay/source' if module == 'RamanujanPV.SelectedReplayAudit' else source
        directory = out/'dependencies'/module
        command = [context['compiler'], '--root='+str(root), '--deps', str(root/rel(module))]
        if write_probes:
            directory.mkdir(parents=True, exist_ok=True)
            cp = subprocess.run(command, capture_output=True, text=True,
                 env=dict(os.environ, LEAN_PATH=':'.join([str(out/'replay/lean'), *generic])))
            for suffix, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
                (directory/suffix).write_text(text)
            save(directory/'PROBE.json', dict(module=module, command=command,
                 returncode=cp.returncode, stdout_sha256=sha(directory/'stdout'),
                 stderr_sha256=sha(directory/'stderr')))
        probe = read(directory/'PROBE.json')
        need(probe['module'] == module and exact(probe['command'], command) and
             type(probe['returncode']) is int and probe['returncode'] == 0,
             'actual independent complete dependency probe')
        for suffix in ['stdout', 'stderr']:
            need(sha(directory/suffix) == probe[suffix+'_sha256'], 'actual dependency output hash')
        imports = roots if module == 'RamanujanPV.SelectedReplayAudit' else \
                  next(q['imports'] for q in order if q['module'] == module)
        required = {(out/'replay/lean'/rel(name).with_suffix('.olean')).resolve()
                    for name in imports if name in seen}
        D.dependency_paths((directory/'stdout').read_text().splitlines(), object_map, generic, required)
        probes.append(probe)
    for index in range(chunks):
        need(exact(result['axioms'][namespace+'.part_'+format(index, '04d')], []),
             'every numerical arithmetic leaf has empty axioms')
    need(exact(result['axioms'][namespace+'.gaps_checked'], []), 'complete prime-gap verification empty axioms')
    if not plan['smoke']:
        text = (out/'replay/audit/CountSourceAudit/stdout').read_text()
        values = [R.payload(line.split('COLD_SOURCE_VALUE_PATH ', 1)[1])
                  for line in text.splitlines() if 'COLD_SOURCE_VALUE_PATH {' in line]
        need(len(values) == 1, 'one actual final source/count proof VALUE graph')
        R.value_payload_check(values[0])
    status = 'PASS_SMOKE_1000_AND_PARAMETERIZED_HIGH_SOURCE_MODEL' if plan['smoke'] else \
             'PASS_FULL_CLEAN_PHYSICAL_COUNT_AND_SOURCE_RUN'
    report = dict(status=status, plan_sha256=sha(out/'PLAN.json'), engine_RESULT_sha256=sha(out/'replay/RESULT.json'),
        wrapper_sha256=sha(HERE/'reproduce.py'), reader_sha256=sha(__file__),
        actual_source_modules=len(order)+1, exact_mathematical_target=target,
        all_numerical_chunks=chunks, actual_dependency_probes=probes,
        fixed_high_output_proved=not plan['smoke'], no_historical_application_objects=True,
        complete_ISO_C_or_physical_program_adequacy_claim=False,
        trust='Actual C bounded surface grammar, program execution model and numerical proof '
              'are connected; generic compiler/ABI/runtime/stdio/OS/hardware and model applicability remain explicit.')
    if not candidate:
        need(exact(read(out/'RESULT.json'), report), 'complete exact independent portable result readback')
    return report
