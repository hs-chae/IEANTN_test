#!/usr/bin/env python3
"""Rebuild the old299 numerical proofs and close the fresh source-run consumer.

Only explicitly validated source-built objects from this campaign form the
basis. The original994 historical objects are replaced by cold695 and new299.
The immutable V2 numerical study, all original workers and all sources remain.
"""
from pathlib import Path
import argparse
import fcntl
import importlib.util
import json
import math
import os
import re
import signal
import subprocess
import sys
import time
import data_stage as D
import source_basis as B

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
ROOT = D.ROOT
NS = D.NS
need, sha, read, save, exact, rel = D.need, D.sha, D.read, D.save, D.exact, D.rel
STD = {'propext', 'Classical.choice', 'Quot.sound'}
GRAMMAR_RESULT = 'cd91e39f0fafecffb75be1babe764cefb98f33d2643a95d4865566f2f7402d3b'
OWNED = {}


def payload(text):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON payload key')
            result[key] = value
        return result
    def finite(text):
        value = float(text)
        need(math.isfinite(value), 'nonfinite JSON payload number')
        return value
    return json.loads(text, object_pairs_hook=pairs, parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def value_payload_check(value):
    need(type(value) is dict and set(value) ==
         {'root', 'required', 'required_count', 'reached_application_and_boundary_constants',
          'checked_value_edges'} and
         value['root'] == 'RHOcticPush.ColdCount.complete_actual_source_run' and
         type(value['checked_value_edges']) is int and value['checked_value_edges'] == 23,
         'all actual finite proof VALUE edges')
    endpoints = ['RamanujanPV.HighTransitionCount.pi_1490000000000'] + [
         'RHOcticPush.CounterSyntax.'+name for name in
         ['checkedCounter_sound', 'checkedDriver_sound', 'counter_render_sound',
          'driver_render_sound', 'expression_sound', 'statement_sound',
          'actual_counter_profile', 'actual_driver_profile']]+[
         'RamanujanPV.QuotientCSourceV2.actual_source_bytes',
         'RHOcticPush.HighDriverSource.actual_source_bytes',
         'RHOcticPush.HighDriverContract.actual_source_model_main']
    need(exact(value['required'], endpoints) and type(value['required_count']) is int and
         value['required_count'] == 12 and
         type(value['reached_application_and_boundary_constants']) is int and
         value['reached_application_and_boundary_constants'] == 23,
         'all exact twelve source/count proof VALUE endpoints, never a selected subset')


def grammar_reader():
    path = ROOT/'Solutions/RHOcticPush.v1/finite-pv/grammar/reproduce.py'
    need(sha(path) == 'c00f09064db3f5915054f1abce991a35a16d8b35ada23b382a696358dcdfe892',
         'immutable source-grammar controller')
    spec = importlib.util.spec_from_file_location('cold_grammar_reader', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def audit_source():
    path = ROOT/'Solutions/RHOcticPush.v1/finite-pv/grammar/CounterSyntaxAudit.lean'
    need(sha(path) == '3c521614c8e8f02ff473ec1f8052d3cf536c326d540cd704faa4a46515afb0c7',
         'accepted independent source value-edge audit')
    text = path.read_text().replace('import CounterGrammarConsumer', 'import CountSourceFinal')
    text = text.replace('let owned := #["CounterGrammar","CounterRendererSound","CounterSourceSyntax","CounterGrammarConsumer"]',
                        'let owned := #["SourceOutputAdapter","DecodedOutputs","HighDecodedOutputs","CountSourceFinal"]')
    text = text.replace('let root := `RHOcticPush.CounterSyntax.complete_canonical_source_run',
                        'let root := `RHOcticPush.ColdCount.complete_actual_source_run')
    text = text.replace('let edges : Array (Name × Array Name) := #[', '''let edges : Array (Name × Array Name) := #[
    (`RHOcticPush.ColdCount.complete_actual_source_run,#[`RHOcticPush.SourceOutputAdapter.canonical_source_output,`RHOcticPush.ColdCount.count]),
    (`RHOcticPush.ColdCount.count,#[`RamanujanPV.HighTransitionCount.pi_1490000000000]),
    (`RHOcticPush.SourceOutputAdapter.canonical_source_output,#[`RHOcticPush.CounterSyntax.complete_canonical_source_run]),''')
    text = text.replace('let required := #[`RHOcticPush.CounterSyntax.checkedCounter_sound,',
                        'let required := #[`RamanujanPV.HighTransitionCount.pi_1490000000000,`RHOcticPush.CounterSyntax.checkedCounter_sound,')
    return text.replace('COUNTER_GRAMMAR_', 'COLD_SOURCE_')


def generated_sources(count_manifest, data_plan):
    C = D.controller()
    result = []
    for module in data_plan['missing_old_parts']:
        index = int(module[-4:])
        size = min(32768, 90670946-index*32768)
        result.append(dict(module=module, kind='arithmetic',
                           text=C.leaf_text(format(index, '04d'), index*32768, size)))
    final = next(q for q in count_manifest['modules'] if q['kind'] == 'final')
    old_source = Path(data_plan['numerical_count'])/'source'/rel(final['module'])
    need(sha(old_source) == final['source_sha256'], 'unchanged original Final source')
    result.append(dict(module=NS+'.Final', kind='final', text=old_source.read_text()))
    for module, path in [('DecodedOutputs', PARENT/'DecodedOutputs.lean'),
                         ('HighDecodedOutputs', PARENT/'HighDecodedOutputs.lean'),
                         ('SourceOutputAdapter', HERE/'SourceOutputAdapter.lean'),
                         ('CountSourceFinal', HERE/'CountSourceFinal.lean.in')]:
        result.append(dict(module=module, kind='consumer', text=path.read_text()))
    result.append(dict(module='CountSourceAudit', kind='audit', text=audit_source()))
    need(len(result) == 305, 'old299 plus Final plus four adapters plus audit')
    return result


def prepare(data_root, grammar, out):
    data_root, grammar, out = data_root.resolve(), grammar.resolve(), out.resolve()
    dp = D.plan_check(data_root)
    need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(data_root)
         and not out.is_relative_to(Path(dp['numerical_count'])) and not out.is_relative_to(ROOT),
         'fresh experiment-owned complement namespace')
    need(sha(grammar/'RESULT.json') == GRAMMAR_RESULT, 'accepted fresh37 grammar/application basis')
    cm = read(Path(dp['numerical_count'])/'MANIFEST.json')
    sources = generated_sources(cm, dp)
    out.mkdir()
    (out/'source').mkdir()
    rows = []
    for item in sources:
        path = out/'source'/rel(item['module'])
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(item['text'])
        rows.append(dict(module=item['module'], kind=item['kind'], sha256=sha(path),
                         imports=D.controller().imports(item['text'])))
    save(out/'PLAN.json', dict(schema='RH_COLD299_FINAL_SOURCE_V1',
         controller_sha256=sha(__file__), data_controller_sha256=sha(HERE/'data_stage.py'),
         source_basis_controller_sha256=sha(HERE/'source_basis.py'),
         data_root=str(data_root), data_plan_sha256=sha(data_root/'PLAN.json'),
         numerical_count=dp['numerical_count'], grammar=str(grammar),
         grammar_result_sha256=GRAMMAR_RESULT, modules=rows,
         source_algorithm='Exact frozen pure-balanced leaf recipe; same original checker propositions.',
         historical_application_objects_admitted=False,
         scope='All695+299 legacy modules replaced; V2 current source-built2469 retained; fresh unchangedFinal and source-indexed exact output.'))
    print('PREPARED_COLD299_AND_FRESH_FINAL_NO_COMPILERS')


def plan_check(out):
    plan = read(out/'PLAN.json')
    need(plan['schema'] == 'RH_COLD299_FINAL_SOURCE_V1'
         and plan['controller_sha256'] == sha(__file__)
         and plan['data_controller_sha256'] == sha(HERE/'data_stage.py') and
         plan['source_basis_controller_sha256'] == sha(HERE/'source_basis.py'),
         'frozen stage controllers')
    dp = D.plan_check(Path(plan['data_root']))
    need(plan['data_plan_sha256'] == sha(Path(plan['data_root'])/'PLAN.json')
         and plan['numerical_count'] == dp['numerical_count'], 'same fixed cold data scope')
    need(sha(Path(plan['grammar'])/'RESULT.json') == plan['grammar_result_sha256'] == GRAMMAR_RESULT,
         'same source-fresh grammar basis')
    cm = read(Path(plan['numerical_count'])/'MANIFEST.json')
    expected = generated_sources(cm, dp)
    C = D.controller()
    want = [dict(module=q['module'], kind=q['kind'],
                 sha256=__import__('hashlib').sha256(q['text'].encode()).hexdigest(),
                 imports=C.imports(q['text'])) for q in expected]
    need(exact(plan['modules'], want), 'canonical complete old299/Final/source consumer recipes')
    for row in want:
        path = out/'source'/rel(row['module'])
        need(path.is_file() and not path.is_symlink() and sha(path) == row['sha256'],
             'frozen prepared source')
        need(path.resolve().is_relative_to(out/'source'), 'owned prepared source ancestry')
    return plan


def basis(plan):
    numerical = Path(plan['numerical_count'])
    cm = read(numerical/'MANIFEST.json')
    data_root = Path(plan['data_root'])
    dr = D.verify(data_root)
    data = read(data_root/'data-replay/RESULT.json')
    cm, transported, transport_receipt = B.transport(numerical, D.plan_check(data_root),
                                                    data['records'])
    grammar = Path(plan['grammar'])
    G = grammar_reader()
    gr = G.validate(grammar)
    maps, collisions = {}, []
    def add(module, source_sha256, obj, origin):
        obj = Path(obj).resolve()
        item = dict(module=module, source_sha256=source_sha256, object=str(obj),
                    object_sha256=sha(obj), origin=origin)
        if module in maps:
            old = maps[module]
            need(old['source_sha256'] == source_sha256, 'same module must have exact same source')
            collisions.append(dict(module=module, selected=old, alternative=item))
        else:
            maps[module] = item
    for row in data['records']:
        if row['module'] == 'RamanujanPV.SelectedReplayAudit':
            continue
        add(row['module'], row['source_sha256'], row['object'],
            dict(study='cold695', result_sha256=sha(data_root/'data-replay/RESULT.json')))
    for row in transported:
        add(row['module'], row['source_sha256'], row['object'],
            dict(study=row['origin'], receipt=row['receipt'],
                 receipt_sha256=row['receipt_sha256']))
    application = Path(gr['foundation']['root'])
    reader = PARENT/'high-driver/readback_complete.py'
    need(sha(reader) == '85a72b6497184963d9f0e058fc7b6cec0fce6971f9b9c73b11ae2f08048ee35b',
         'accepted complete application source/resource reader')
    spec = importlib.util.spec_from_file_location('cold_complete_application', reader)
    complete_reader = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(complete_reader)
    complete_reader.verify(application)
    app = read(application/'RESULT.json')
    for row in app['build']:
        add(row['module'], row['source_sha256'], application/'objects'/rel(row['module']).with_suffix('.olean'),
            dict(study='fresh32-application', result_sha256=sha(application/'RESULT.json')))
    for row in gr['build']:
        add(row['module'], row['source_sha256'], grammar/'objects'/rel(row['module']).with_suffix('.olean'),
            dict(study='fresh5-grammar', result_sha256=sha(grammar/'RESULT.json')))
    expected_parts = {NS+'.Check'+format(i, '04d') for i in range(2768)}
    new_parts = {q['module'] for q in plan['modules'] if q['kind'] == 'arithmetic'}
    basis_parts = {name for name in maps if name.startswith(NS+'.Check')}
    need(not (new_parts & basis_parts) and new_parts | basis_parts == expected_parts,
         'all and only2768 exact numerical chunks, with original299 truly absent from basis')
    need(all(name in maps for name in D.data_inputs(cm)), 'all695 source-fresh data/gap modules')
    need(not any(name in cm['basis'] and name not in D.data_inputs(cm) for name in maps),
         'no historical299 proof object admitted')
    return maps, collisions, cm['context'], dict(numerical_RESULT_sha256=sha(numerical/'RESULT.json'),
         current_source_transport=transport_receipt,
         cold_DATA_RESULT_sha256=__import__('hashlib').sha256(
             __import__('json').dumps(dr, sort_keys=True).encode()).hexdigest(),
         grammar_RESULT_sha256=sha(grammar/'RESULT.json'))


def required(row):
    if row['kind'] == 'arithmetic':
        return [NS+'.part_'+row['module'][-4:]]
    if row['kind'] == 'final':
        return [NS+'.pi_1490000000000']
    if row['module'] == 'SourceOutputAdapter':
        return ['RHOcticPush.SourceOutputAdapter.'+x
                for x in ['canonical_source_output', 'every_source_output']]
    if row['module'] == 'CountSourceFinal':
        return ['RHOcticPush.ColdCount.'+x for x in ['count', 'complete_actual_source_run',
                'every_actual_source_output', 'all_finished_pi', 'all_finished_source_function']]
    return []


def memory(row):
    if row['kind'] == 'arithmetic':
        return 128 << 30
    if row['module'] in ['DecodedOutputs', 'HighDecodedOutputs', 'SourceOutputAdapter']:
        return 64 << 30
    return 256 << 30


def command(out, context, row, attempt, cpu):
    return ['taskset', '-c', str(cpu), '/usr/bin/prlimit', '--as='+str(memory(row)), '--',
            '/usr/bin/time', '-v', '-o', str(attempt/'resources'), context['compiler'],
            '--root='+str(out/'source'), '-j1', str(out/'source'/rel(row['module'])),
            '-o', str(out/'objects'/rel(row['module']).with_suffix('.olean'))]


def probe(out, context, row, attempt, maps):
    cmd = [context['compiler'], '--root='+str(out/'source'), '--deps',
           str(out/'source'/rel(row['module']))]
    cp = subprocess.run(cmd, capture_output=True, text=True,
                        env=dict(os.environ, LEAN_PATH=':'.join([str(out/'union'),
                                                               *context['generic_libraries']])))
    need(cp.returncode == 0, 'actual dependency compiler status')
    for suffix, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
        (attempt/('deps.'+suffix)).write_text(text)
    lines = cp.stdout.splitlines()
    need(lines and all(line.strip() for line in lines), 'nonempty actual dependency pathname')
    actual = {Path(x).resolve() for x in lines}
    need(actual, 'nonempty actual dependency inventory')
    generic = [Path(x).resolve() for x in context['generic_libraries']]
    generic.append(Path(context['compiler']).resolve().parents[1]/'lib/lean')
    allowed = {Path(q['object']).resolve(): q['object_sha256'] for q in maps.values()}
    for path in actual:
        need(any(path.is_relative_to(g) for g in generic)
             or path in allowed and sha(path) == allowed[path], 'foreign application dependency')
        if path not in allowed:
            need(not any(part in {'RamanujanPV', 'LCMSourcePV', 'RHOcticPush'}
                         for part in path.parts), 'application cannot masquerade as generic library')
    need({Path(maps[name]['object']).resolve() for name in row['imports'] if name in maps} <= actual,
         'every declared direct application import')
    return dict(command=cmd, returncode=cp.returncode, stdout_sha256=sha(attempt/'deps.stdout'),
                stderr_sha256=sha(attempt/'deps.stderr'))


def receipt_check(out, row, record, context, maps):
    C = D.controller()
    attempt = Path(record['attempt'])
    need(attempt.is_relative_to(out/'attempts'/row['module']) and
         attempt.parent == out/'attempts'/row['module'] and attempt.name.isdigit(),
         'exact owned actual compiler attempt path')
    need(record['module'] == row['module'] and type(record['returncode']) is int
         and record['returncode'] == 0, 'exact successful actual compiler identity')
    need(record['source_sha256'] == row['sha256'] == sha(out/'source'/rel(row['module'])),
         'frozen source association')
    obj = out/'objects'/rel(row['module']).with_suffix('.olean')
    need(obj.is_file() and not obj.is_symlink() and sha(obj) == record['object_sha256'],
         'fresh owned compiled object')
    need(obj.resolve().is_relative_to(out/'objects') and
         attempt.resolve().is_relative_to(out/'attempts'), 'owned compiler object/log ancestry')
    need(exact(record['command'], command(out, context, row, attempt, record['cpu'])),
         'actual source/compiler/object command')
    need(type(record['cpu']) is int and record['cpu'] in range(32, 64),
         'strict actual owned CPU lane')
    for suffix in ['stdout', 'stderr', 'resources']:
        need(sha(attempt/suffix) == record[suffix+'_sha256'], 'actual compiler receipt log')
    usage = (attempt/'resources').read_text()
    match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
    need(match is not None and type(record['peak_RSS_KiB']) is int
         and int(match[1]) == record['peak_RSS_KiB'], 'actual child RAM high-water mark')
    need(type(record['seconds']) in [int, float] and math.isfinite(record['seconds'])
         and record['seconds'] >= 0, 'finite nonnegative observed duration')
    D.observed_wall(usage, record['seconds'])
    need(record['peak_RSS_KiB'] > 0 and record['peak_RSS_KiB']*1024 <= memory(row),
         'actual RAM bounded by executed address-space cap')
    output = (attempt/'stdout').read_text()+(attempt/'stderr').read_text()
    need(not any(token in output for token in
                 ['sorryAx', 'Lean.ofReduceBool', 'declaration uses `sorry`']),
         'no admitted or native execution proof leaf')
    axioms = C.reports((attempt/'stdout').read_text(), required(row), row['kind'] == 'arithmetic')
    need(exact(axioms, record['axioms']), 'actual empty/standard theorem axiom reports')
    actual_probe = probe(out, context, row, attempt, maps)
    need(exact(actual_probe, record['dependency_probe']), 'fresh actual dependency readback')
    return record


def validate(out, candidate=None):
    plan = plan_check(out)
    result = read(candidate or out/'RESULT.json')
    need(result['status'] == 'PASS_NO_OLD_APPLICATION_CACHE_COUNT_AND_SOURCE_RUN', 'no partial acceptance')
    need(result['controller_sha256'] == sha(__file__) == sha(out/'remaining.executed.py')
         and result['plan_sha256'] == sha(out/'PLAN.json'), 'controller/plan identity')
    maps, collisions, context, provenance = basis(plan)
    need(exact(result['foundation'], provenance) and exact(read(out/'BASIS.json')['collisions'], collisions),
         'same explicitly current-campaign source basis and collision choices')
    need([q['module'] for q in result['records']] == [q['module'] for q in plan['modules']],
         'complete exact305 module population')
    for row, got in zip(plan['modules'], result['records']):
        receipt_check(out, row, got, context, maps)
        maps[row['module']] = dict(module=row['module'], source_sha256=row['sha256'],
            object=str(out/'objects'/rel(row['module']).with_suffix('.olean')),
            object_sha256=got['object_sha256'])
    audit = next(q for q in result['records'] if q['module'] == 'CountSourceAudit')
    text = (Path(audit['attempt'])/'stdout').read_text()
    rows = [payload(line.split('COLD_SOURCE_THEOREM ', 1)[1])
            for line in text.splitlines() if 'COLD_SOURCE_THEOREM {' in line]
    totals = re.findall(r'COLD_SOURCE_AUDIT_PASS (\d+)', text)
    need(len(totals) == 1 and int(totals[0]) == len(rows) > 0
         and len({q['name'] for q in rows}) == len(rows), 'complete unique compiler theorem audit')
    for q in rows:
        need(type(q) is dict and set(q) == {'name', 'module', 'axioms'} and
             type(q['name']) is str and q['name'] and type(q['module']) is str and
             q['module'] in ['SourceOutputAdapter', 'DecodedOutputs', 'HighDecodedOutputs',
                             'CountSourceFinal'] and type(q['axioms']) is list and
             all(type(value) is str and value in STD for value in q['axioms']) and
             len(q['axioms']) == len(set(q['axioms'])),
             'strict unique actual source/consumer theorem axiom rows')
    need(set(required(next(q for q in plan['modules'] if q['module'] == 'CountSourceFinal')))
         <= {q['name'] for q in rows}, 'all five closed final consumer theorem roots')
    need('COLD_SOURCE_VALUE_PATH ' in text, 'actual source/count proof VALUE path')
    payloads = [payload(line.split('COLD_SOURCE_VALUE_PATH ', 1)[1])
                for line in text.splitlines() if 'COLD_SOURCE_VALUE_PATH {' in line]
    need(len(payloads) == 1, 'one actual source/count proof VALUE payload')
    value_payload_check(payloads[0])
    need(result['no_historical_application_objects'] is True
         and result['complete_ISO_C_or_physical_PV_claim'] is False, 'precise source/model trust scope')
    need(type(result['seconds']) in [int, float] and math.isfinite(result['seconds']) and
         result['seconds'] >= 0 and sha(out/'RESOURCE_SAMPLES.jsonl') ==
         result['RESOURCE_SAMPLES_sha256'], 'actual measured resource log and duration')
    for value in result['resource_peaks'].values():
        need(type(value) is int and value >= 0, 'strict observed aggregate resource counters')
    need(result['resource_peaks']['disk'] <= 300*(1 << 30), 'owned scratch cap')
    return result


def drain_unexpected(out, error):
    C = D.controller()
    events = []
    for pid, item in list(OWNED.items()):
        if item['process'].poll() is not None:
            continue
        current = C.process(pid)
        need(current is not None and current['start_ticks'] == item['start_ticks'],
             'exact owned process identity before failure cleanup')
        os.killpg(pid, signal.SIGTERM)
        events.append(dict(pid=pid, start_ticks=item['start_ticks'], signal='SIGTERM'))
    for item in OWNED.values():
        if item['process'].poll() is None:
            try:
                item['process'].wait(timeout=30)
            except subprocess.TimeoutExpired:
                pid = item['process'].pid
                current = C.process(pid)
                need(current is not None and current['start_ticks'] == item['start_ticks'],
                     'exact owned process identity before final failure cleanup')
                os.killpg(pid, signal.SIGKILL)
                item['process'].wait()
                events.append(dict(pid=pid, start_ticks=item['start_ticks'], signal='SIGKILL',
                                   reason='owned compiler did not stop after SIGTERM; not OOM attribution'))
        item['stdout'].close()
        item['stderr'].close()
    save(out/('FAILURE-'+str(time.time_ns())+'.json'), dict(error=repr(error),
         status='NO_ACCEPTANCE_OWNED_PROCESSES_DRAINED', owned_cleanup=events))


def run(out, jobs, resume):
    plan = plan_check(out)
    need(type(jobs) is int and 1 <= jobs <= 22, 'bounded source proof lanes')
    lock = (out/'STAGE.lock').open('a')
    fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    need(not (out/'RESULT.json').exists(), 'accepted result immutable')
    maps, collisions, context, provenance = basis(plan)
    C = D.controller()
    need(C.available() >= 550*(1 << 30), '512GiB reserve plus safe physical job headroom')
    need(__import__('shutil').disk_usage(out).free >= 1 << 40, 'separate disk admission')
    for name in ['objects', 'union', 'attempts']:
        (out/name).mkdir(exist_ok=True)
    if (out/'remaining.executed.py').exists():
        need(resume and sha(out/'remaining.executed.py') == sha(__file__), 'explicit exact-source resume')
    else:
        (out/'remaining.executed.py').write_bytes(Path(__file__).read_bytes())
    save(out/'BASIS.json', dict(modules=maps, collisions=collisions, provenance=provenance))
    for name, item in maps.items():
        path = out/'union'/rel(name).with_suffix('.olean')
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.is_symlink():
            need(path.resolve() == Path(item['object']).resolve(), 'same explicit basis object')
        else:
            need(not path.exists(), 'no foreign basis object')
            path.symlink_to(item['object'])
    records, active, drain = {}, {}, []
    by = {q['module']: q for q in plan['modules']}
    for row in plan['modules']:
        accepted = out/'attempts'/row['module']/'ACCEPTED.json'
        if accepted.exists():
            need(resume, 'explicit continuation required')
            got = receipt_check(out, row, read(accepted), context, maps)
            records[row['module']] = got
            maps[row['module']] = dict(module=row['module'], source_sha256=row['sha256'],
                object=str(out/'objects'/rel(row['module']).with_suffix('.olean')),
                object_sha256=got['object_sha256'])
            link = out/'union'/rel(row['module']).with_suffix('.olean')
            link.parent.mkdir(parents=True, exist_ok=True)
            if not link.exists():
                link.symlink_to(maps[row['module']]['object'])
    def stop(sig, frame):
        drain.append(signal.Signals(sig).name)
    for sig in [signal.SIGINT, signal.SIGTERM, signal.SIGUSR1]:
        signal.signal(sig, stop)
    cpus = list(range(32, 64))
    need(set(cpus) <= os.sched_getaffinity(0), 'actual independent CPU lanes')
    env = dict(os.environ, LEAN_PATH=':'.join([str(out/'union'), *context['generic_libraries']]),
               PYTHONDONTWRITEBYTECODE='1')
    start = time.monotonic()
    peaks = dict(RSS=0, PSS=0, individual_RSS=0, individual_VmPeak=0, disk=C.disk(out))
    with (out/'RESOURCE_SAMPLES.jsonl').open('a') as samples:
        while len(records) < len(by):
            observed = C.process_tree(os.getpid(), True)
            rss, pss = sum(q.get('VmRSS', 0) for q in observed), sum(q.get('Pss', 0) for q in observed)
            peaks['RSS'], peaks['PSS'] = max(peaks['RSS'], rss), max(peaks['PSS'], pss)
            peaks['individual_RSS'] = max([peaks['individual_RSS']]+[q.get('VmRSS', 0) for q in observed])
            peaks['individual_VmPeak'] = max([peaks['individual_VmPeak']]+[q.get('VmPeak', 0) for q in observed])
            peaks['disk'] = max(peaks['disk'], C.disk(out))
            samples.write(__import__('json').dumps(dict(unix=time.time(), RSS=rss, PSS=pss,
                 processes=observed, active=len(active), MemAvailable=C.available(), disk=peaks['disk']))+'\n')
            samples.flush()
            need(peaks['disk'] <= 300*(1 << 30), 'owned scratch cap')
            if C.available() < 512*(1 << 30) and active:
                name = max(active, key=lambda key: active[key]['start'])
                owned = active[name]
                current = C.process(owned['process'].pid)
                need(current is not None and current['start_ticks'] == owned['start_ticks'],
                     'exact owned identity before host-reserve stop')
                os.killpg(owned['process'].pid, signal.SIGTERM)
                drain.append('HOST_RESERVE_RESOURCE_STOP')
            for name, item in list(active.items()):
                code = item['process'].poll()
                if code is None:
                    continue
                item['stdout'].close()
                item['stderr'].close()
                row, attempt = by[name], item['attempt']
                record = dict(module=name, attempt=str(attempt), returncode=code,
                    command=item['command'], cpu=item['cpu'], seconds=time.monotonic()-item['start'],
                    source_sha256=sha(out/'source'/rel(name)),
                    **{suffix+'_sha256': sha(attempt/suffix) for suffix in ['stdout', 'stderr', 'resources']})
                usage = (attempt/'resources').read_text()
                match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
                record['peak_RSS_KiB'] = int(match[1]) if match else None
                save(attempt/'RAW.json', record)
                if code != 0:
                    drain.append('FAILED_COMPILER_ATTEMPT_PRESERVED')
                    del active[name]
                    OWNED.pop(item['process'].pid, None)
                    continue
                record['object_sha256'] = sha(out/'objects'/rel(name).with_suffix('.olean'))
                record['axioms'] = C.reports((attempt/'stdout').read_text(), required(row), row['kind'] == 'arithmetic')
                record['dependency_probe'] = probe(out, context, row, attempt, maps)
                receipt_check(out, row, record, context, maps)
                save(attempt/'RECEIPT.json', record)
                save(attempt.parent/'ACCEPTED.json', record)
                records[name] = record
                maps[name] = dict(module=name, source_sha256=row['sha256'],
                    object=str(out/'objects'/rel(name).with_suffix('.olean')),
                    object_sha256=record['object_sha256'])
                link = out/'union'/rel(name).with_suffix('.olean')
                link.parent.mkdir(parents=True, exist_ok=True)
                need(not link.exists(), 'fresh new proof namespace')
                link.symlink_to(maps[name]['object'])
                del active[name]
                OWNED.pop(item['process'].pid, None)
                print(len(records), len(by), name, round(record['seconds'], 2), flush=True)
            if drain and not active:
                save(out/'STOPPED.json', dict(status='DRAINED_NOT_ACCEPTANCE', reasons=drain,
                                             completed=len(records)))
                return
            if not drain:
                budget = max([math.ceil(39.6*(1 << 30))]+[
                    math.ceil(q['peak_RSS_KiB']*1024*1.2) for q in records.values()
                    if by[q['module']]['kind'] == 'arithmetic'])
                used = {item['cpu'] for item in active.values()}
                for row in plan['modules']:
                    name = row['module']
                    if len(active) >= jobs:
                        break
                    if name in records or name in active:
                        continue
                    need(all(dep in maps or dep in by or dep.split('.')[0] in
                             ['Lean', 'Init', 'Std', 'Mathlib'] for dep in row['imports']),
                         'complete declared source dependency scope')
                    if any(dep in by and dep not in records for dep in row['imports']):
                        continue
                    heavy = row['kind'] in ['final', 'audit'] or row['module'] == 'CountSourceFinal'
                    if heavy and active:
                        continue
                    growth = sum(max(0, budget-sum(q.get('VmRSS', 0) for q in
                                 C.process_tree(item['process'].pid))) for item in active.values())
                    physical = 256*(1 << 30) if heavy else budget
                    if C.available() < 512*(1 << 30)+growth+physical:
                        break
                    cpu = next(q for q in cpus if q not in used)
                    parent = out/'attempts'/name
                    parent.mkdir(parents=True, exist_ok=True)
                    index = 1
                    while (parent/str(index)).exists():
                        index += 1
                    attempt = parent/str(index)
                    attempt.mkdir()
                    obj = out/'objects'/rel(name).with_suffix('.olean')
                    obj.parent.mkdir(parents=True, exist_ok=True)
                    cmd = command(out, context, row, attempt, cpu)
                    stdout, stderr = (attempt/'stdout').open('w'), (attempt/'stderr').open('w')
                    process = subprocess.Popen(cmd, cwd=out/'source', env=env, stdout=stdout,
                                               stderr=stderr, start_new_session=True)
                    active[name] = dict(process=process, attempt=attempt, command=cmd, cpu=cpu,
                                        stdout=stdout, stderr=stderr, start=time.monotonic(),
                                        start_ticks=C.process(process.pid)['start_ticks'])
                    OWNED[process.pid] = active[name]
                    used.add(cpu)
                    if heavy:
                        break
            save(out/'RUN_STATE.json', dict(completed=len(records), total=len(by),
                 active=[dict(module=name, pid=x['process'].pid, start_ticks=x['start_ticks'])
                         for name, x in active.items()], resource_peaks=peaks,
                 drain=drain, elapsed_seconds=time.monotonic()-start))
            time.sleep(1)
    result = dict(status='PASS_NO_OLD_APPLICATION_CACHE_COUNT_AND_SOURCE_RUN',
        controller_sha256=sha(__file__), plan_sha256=sha(out/'PLAN.json'), foundation=provenance,
        records=[records[q['module']] for q in plan['modules']], seconds=time.monotonic()-start,
        resource_peaks=peaks, RESOURCE_SAMPLES_sha256=sha(out/'RESOURCE_SAMPLES.jsonl'),
        no_historical_application_objects=True, complete_ISO_C_or_physical_PV_claim=False)
    save(out/'CANDIDATE.json', result)
    validate(out, out/'CANDIDATE.json')
    save(out/'RESULT.json', result)
    print(result['status'])


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--data', type=Path)
    parser.add_argument('--grammar', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=22)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    need(sum([args.prepare, args.run, args.verify, args.check]) == 1, 'one explicit operation')
    if args.prepare:
        need(args.data is not None and args.grammar is not None and not args.resume,
             'explicit prepared data and source-fresh grammar')
        prepare(args.data, args.grammar, args.out)
    else:
        need(args.data is None and args.grammar is None, 'fixed prepared foundation identities')
        out = args.out.resolve()
        if args.run:
            try:
                run(out, args.jobs, args.resume)
            except BaseException as error:
                drain_unexpected(out, error)
                raise
        elif args.check:
            plan_check(out)
            print('PASS_PREPARED299_CANONICAL_SOURCES_NO_COMPILERS')
        else:
            print(__import__('json').dumps(validate(out), sort_keys=True))


if __name__ == '__main__':
    main()
