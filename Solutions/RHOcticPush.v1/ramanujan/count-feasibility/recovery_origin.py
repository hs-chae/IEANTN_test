#!/usr/bin/env python3
"""Exact partial-origin transport for a separate resource-only count recovery.

No original receipt/source/object is rewritten. Reused proofs retain their
actual original compiler commands; every proof receives an actual dependency
probe whose logs and complete object population are read back independently.
"""
from pathlib import Path
import hashlib, importlib.util, json, os, shutil, subprocess

HERE = Path(__file__).resolve().parent
V1_SHA = 'a58fe8105587ea9b94beace2d5c6ab29b3225e9b9bea023d65e0cf78f29b61b1'
ORIGIN = Path('/data/ivy-rh-octic-20261123/ramanujan/pure-count-recovery-v1')

def exact(left, right):
    """JSON identity, including bool/int/float distinctions that Python == loses."""
    return json.dumps(left, sort_keys=True, allow_nan=False) == \
        json.dumps(right, sort_keys=True, allow_nan=False)

def engine():
    p = HERE/'recover_count.py'
    if hashlib.sha256(p.read_bytes()).hexdigest() != V1_SHA:
        raise ValueError('immutable original controller drift')
    spec = importlib.util.spec_from_file_location('immutable_count_recovery_v1', p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

def drained(v, root):
    stop = v.read(root/'STOPPED.json')
    v.need(stop['status'] == 'DRAINED_INCOMPLETE_NOT_ACCEPTANCE' and
           exact(stop['reasons'], ['SIGUSR1']) and exact(stop['failures'], []),
           'only clean requested origin drain, no hidden failed recovery')
    state = v.read(root/'RUN_STATE.json')
    # V1's final RUN_STATE can precede its last compiler completion. Its
    # immutable END/STOPPED receipts and actual PID/start tokens close that gap.
    v.need(exact(state['failures_this_attempt'], []), 'no hidden origin compiler failure')
    for item in state['active']:
        v.need(type(item['pid']) is int and type(item['start_ticks']) is str and
               item['start_ticks'].isdigit(), 'strict original process identity')
        actual = v.process(item['pid'])
        v.need(actual is None or actual['start_ticks'] != item['start_ticks'],
               'recorded original compiler is still active')
    live = v.read(root/'LIVE_IDENTITY.json')
    v.need(type(live['pid']) is int and type(live['start_ticks']) is str and
           live['start_ticks'].isdigit(), 'strict original controller identity')
    row = v.process(live['pid'])
    if row is not None and row['start_ticks'] == live['start_ticks']:
        status = Path('/proc', str(live['pid']), 'stat').read_text().rsplit(')', 1)[1].split()[0]
        v.need(status == 'Z', 'original controller is still active')
    v.need(not (root/'RESULT.json').exists(), 'completed origin must not be migrated')
    attempts = sorted((root/'CONTROLLER_ATTEMPTS').glob('*/END.json'))
    v.need(bool(attempts), 'complete origin controller-attempt history')
    final = max((v.read(p) for p in attempts), key=lambda x: x['unix'])
    v.need(exact(final['drain_this_attempt'], ['SIGUSR1']) and
           exact(final['failures_this_attempt'], []) and final['final_acceptance'] is False,
           'actual clean final controller end receipt')
    return {str(p.relative_to(root)): v.sha(p) for p in
            [root/'STOPPED.json', root/'RUN_STATE.json', root/'LIVE_IDENTITY.json', *attempts]}

def accepted(v, root, m):
    records = []
    for q in m['modules']:
        path = root/'attempts'/q['module']/'ACCEPTED.json'
        if not path.exists():
            continue
        row = v.read(path)
        receipt = Path(row['receipt'])
        v.need(receipt.is_relative_to(root/'attempts'/q['module']), 'owned origin compiler receipt')
        actual = v.audit_receipt(root, m, q, receipt)
        v.need(type(actual['returncode']) is int and type(actual['peak_RSS_bytes']) is int,
               'strict original compiler/resource integer measurements')
        v.need(exact(actual, row['proof']),
               'independent exact original compiler/proof readback')
        records.append(row)
    names = {row['module'] for row in records}
    for q in m['modules']:
        if q['module'] in names:
            v.need(set(q['imports']) & {x['module'] for x in m['modules']} <= names,
                   'downward-closed accepted origin proof DAG')
    return records

def object_map(v, root, m, records):
    result = {Path(q['object']).resolve(): q['object_sha256'] for q in m['basis'].values()}
    for row in records:
        p = root/'objects'/v.rel(row['module'], '.olean')
        v.need(v.sha(p) == row['proof']['object_sha256'], 'exact reused proof object')
        result[p.resolve()] = row['proof']['object_sha256']
    return result

def dependency_probe(v, source_root, union, context, module, target):
    target.mkdir(parents=True, exist_ok=True)
    cmd = [context['compiler'], '--root='+str(source_root), '--deps',
           str(source_root/v.rel(module))]
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(union), *context['generic_libraries']])
    cp = subprocess.run(cmd, cwd=source_root, env=env, capture_output=True, text=True)
    (target/'stdout').write_text(cp.stdout)
    (target/'stderr').write_text(cp.stderr)
    v.need(cp.returncode == 0, 'actual per-proof dependency probe')
    return dict(module=module, command=cmd, returncode=cp.returncode,
                stdout_sha256=v.sha(target/'stdout'), stderr_sha256=v.sha(target/'stderr'))

def audit_probe(v, probe, source_root, context, target, objects, required=()):
    mod = probe['module']
    v.need(type(probe['returncode']) is int and probe['returncode'] == 0,
           'actual probe status, never JSON boolean')
    v.need(probe['command'] == [context['compiler'], '--root='+str(source_root), '--deps',
                               str(source_root/v.rel(mod))], 'exact source dependency command')
    for suffix in ['stdout', 'stderr']:
        v.need(v.sha(target/suffix) == probe[suffix+'_sha256'], 'dependency log hash')
    generic = [Path(p).resolve() for p in context['generic_libraries']]
    generic.append(Path(context['compiler']).resolve().parents[1]/'lib/lean')
    found = set()
    lines = (target/'stdout').read_text().splitlines()
    v.need(bool(lines), 'nonempty actual dependency output')
    for line in lines:
        v.need(bool(line.strip()), 'nonempty dependency pathname')
        p = Path(line).resolve()
        found.add(p)
        if any(p.is_relative_to(g) for g in generic):
            continue
        v.need(p in objects and v.sha(p) == objects[p], 'foreign or drifted application dependency')
    v.need(set(required) <= found, 'missing actual direct application import')

def direct_imports(v, root, m, module):
    row = next(q for q in m['modules'] if q['module'] == module)
    application = {q['module'] for q in m['modules']}
    result = []
    for name in row['imports']:
        if name in m['basis']:
            result.append(Path(m['basis'][name]['object']).resolve())
        elif name in application:
            result.append((root/'objects'/v.rel(name, '.olean')).resolve())
    return result

def prepare(e, origin, out):
    v = engine()
    origin, out = origin.resolve(), out.resolve()
    e.need(origin == ORIGIN and not out.exists(), 'fixed original and fresh recovery namespace')
    e.need(out.parent == ORIGIN.parent, 'owned sibling output namespace')
    before = e.sha(e.__file__)
    old = v.manifest(origin)
    drain_files = drained(v, origin)
    records = accepted(v, origin, old)
    e.need(records and len(records) < len(old['modules']), 'genuine incomplete accepted origin')
    out.mkdir()
    for name in ['objects', 'union', 'attempts', 'dependencies', 'origin-dependencies']:
        (out/name).mkdir()
    shutil.copytree(origin/'source', out/'source', symlinks=False)
    shutil.copy2(origin/'ORIGINAL_CHECKPOINT.json', out/'ORIGINAL_CHECKPOINT.json')
    shutil.copy2(e.__file__, out/'recover_count.executed.py')
    shutil.copy2(__file__, out/'recovery_origin.executed.py')
    objects = object_map(v, origin, old, records)
    probes = []
    for row in records:
        mod = row['module']
        probe = dependency_probe(v, origin/'source', origin/'union', old['context'],
                                 mod, out/'origin-dependencies'/mod)
        audit_probe(v, probe, origin/'source', old['context'],
                    out/'origin-dependencies'/mod, objects,
                    direct_imports(v, origin, old, mod))
        probes.append(probe)
        obj = out/'objects'/v.rel(mod, '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.symlink_to(origin/'objects'/v.rel(mod, '.olean'))
        p = out/'attempts'/mod/'ACCEPTED.json'
        p.parent.mkdir(parents=True, exist_ok=True)
        v.save(p, row)
    for name, row in old['basis'].items():
        target = out/'union'/v.rel(name, '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(row['object'])
    checkpoint = dict(origin=str(origin), manifest_sha256=v.sha(origin/'MANIFEST.json'),
        original_controller_sha256=V1_SHA, drain_files=drain_files, records=records,
        dependency_probes=probes, resource_samples_sha256=v.sha(origin/'RESOURCE_SAMPLES.jsonl'),
        dispatch_sha256=v.sha(origin/'DISPATCH.jsonl'),
        history=v.historical_evidence(origin))
    v.save(out/'ORIGIN_CHECKPOINT.json', checkpoint)
    m = dict(old)
    m['controller_sha256'] = before
    m['prior_origin'] = dict(root=str(origin), checkpoint_sha256=v.sha(out/'ORIGIN_CHECKPOINT.json'),
                            helper_sha256=v.sha(__file__), accepted=len(records))
    m['resource_policy'] = dict(old['resource_policy'], max_jobs=22,
                               initial_MinAvailable_bytes=550*v.G,
                               source='Resource-only supplemental continuation; original initial1TiB admission retained in origin.')
    v.need(before == e.sha(e.__file__), 'new controller stable during origin transport')
    v.save(out/'MANIFEST.json', m)
    v.save(out/'PLAN.json', dict(status='PREPARED_RESOURCE_ONLY_22_MAX_ADAPTIVE_NOT_LAUNCHED',
        scientific_module_inventory_unchanged=True, source_generator_sha256=V1_SHA,
        new_controller_sha256=before, manifest_sha256=v.sha(out/'MANIFEST.json'),
        origin_reused_modules=len(records), total_new_module_inventory=len(old['modules']),
        host_reserve_bytes=512*v.G, max_jobs=22))
    return m

def validate_origin(e, out, m):
    v = engine()
    o = m['prior_origin']
    e.need(Path(o['root']).resolve() == ORIGIN, 'fixed independently preserved original')
    e.need(e.sha(__file__) == o['helper_sha256'] == e.sha(out/'recovery_origin.executed.py'),
           'exact origin transport implementation')
    e.need(e.sha(out/'ORIGIN_CHECKPOINT.json') == o['checkpoint_sha256'], 'frozen origin checkpoint')
    c = e.read(out/'ORIGIN_CHECKPOINT.json')
    origin = Path(c['origin'])
    e.need(origin == ORIGIN and e.sha(origin/'MANIFEST.json') == c['manifest_sha256'],
           'actual original manifest binding')
    old = v.manifest(origin)
    e.need(c['original_controller_sha256'] == V1_SHA and exact(m['modules'], old['modules'])
           and exact(m['basis'], old['basis']) and exact(m['resources'], old['resources'])
           and exact(m['context'], old['context'])
           and m['generator_sha256'] == old['generator_sha256'], 'unchanged scientific proof/source universe')
    e.need(exact(drained(v, origin), c['drain_files']), 'immutable clean origin drain')
    records = accepted(v, origin, old)
    e.need(exact(records, c['records']) and type(o['accepted']) is int and
           len(records) == o['accepted'], 'complete immutable origin proof set')
    e.need(e.sha(origin/'RESOURCE_SAMPLES.jsonl') == c['resource_samples_sha256'] and
           e.sha(origin/'DISPATCH.jsonl') == c['dispatch_sha256'] and
           exact(v.historical_evidence(origin), c['history']), 'all original attempts and resource history')
    e.need(exact([q['module'] for q in c['dependency_probes']], [q['module'] for q in records]),
           'one actual dependency probe per reused proof')
    objects = object_map(v, origin, old, records)
    for probe in c['dependency_probes']:
        audit_probe(v, probe, origin/'source', old['context'],
                    out/'origin-dependencies'/probe['module'], objects,
                    direct_imports(v, origin, old, probe['module']))
    for row in records:
        obj = out/'objects'/e.rel(row['module'], '.olean')
        e.need(obj.is_symlink() and obj.resolve() ==
               (origin/'objects'/e.rel(row['module'], '.olean')).resolve(),
               'explicit origin object association')
    return v, old, {row['module']: row for row in records}, c
