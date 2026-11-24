#!/usr/bin/env python3
"""Fresh source compilation of all695 legacy data/gap modules.

The frozen existing source-only replay engine is reused unchanged. No original
application object is admitted to this stage. Preparation may run while the
main count is active; compilation requires its complete accepted result first.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import importlib.util
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
ROOT = HERE.parents[4]
COUNT_MANIFEST = '0e7e863f1df8d527d56f70213206f801b96e322fa4e5a013cf0486a540e914e3'
COUNT_CONTROLLER = '299b7a6ec84049af35c18f6e0cff2515b9115d49fbdd8cf7d0917c4564d16838'
NS = 'RamanujanPV.HighTransitionCount'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(8 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def finite(text):
        value = float(text)
        need(math.isfinite(value), 'nonfinite JSON number')
        return value
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def save(path, value):
    path = Path(path)
    temporary = path.with_name('.'+path.name+'.pending')
    need(not temporary.exists(), 'fresh atomic receipt temporary')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(temporary, path)


def exact(left, right):
    def encode(value):
        return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)
    return encode(left) == encode(right)


def observed_wall(usage, seconds):
    match = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', usage)
    need(match is not None and type(seconds) in [int, float] and
         math.isfinite(seconds) and seconds >= 0, 'finite actual GNU-time wall evidence')
    parts = match[1].split(':')
    need(len(parts) in [2, 3], 'canonical GNU-time duration')
    wall = sum(float(value)*60**index for index, value in enumerate(reversed(parts)))
    # Controller completion timestamps include polling and earlier receipt work.
    need(wall-.1 <= seconds <= wall+max(60, wall/2),
         'observed completion duration agrees with GNU-time within polling allowance')
    return wall


def owned_file(actual_path, expected_path, scope, expected_sha):
    path = Path(expected_path)
    need(actual_path == str(path) and path.is_file() and not path.is_symlink() and
         path.resolve().is_relative_to(scope) and sha(path) == expected_sha,
         'owned regular actual replay file')


def dependency_paths(lines, object_map, generic, required):
    need(lines and all(line.strip() for line in lines), 'nonempty dependency paths')
    found = {Path(line).resolve() for line in lines}
    for path in found:
        if path in object_map:
            continue
        need(any(path.is_relative_to(Path(g).resolve()) for g in generic) and
             not any(part in {'RamanujanPV', 'LCMSourcePV', 'RHOcticPush'}
                     for part in path.parts), 'no historical/foreign application dependency')
    need(set(required) <= found, 'every actual declared direct application import')
    return found


def rel(module):
    return Path(*module.split('.')).with_suffix('.lean')


def data_inputs(original):
    return {name: row for name, row in original['basis'].items()
            if name.rsplit('.', 1)[1].startswith('Data')
            or name in [NS+'.Gaps', NS+'.GapCheck']}


def execution_command(out, context, python):
    return [python, str(out/'engine/Solutions/Replay/scripts/reproduce_profiled_closure.py'),
            '--context', str(context), '--out', str(out/'data-replay'),
            '--application-source-root', str(out/'source'), '--root', NS+'.GapCheck',
            '--theorem', NS+'.gaps_checked', '--jobs', '32',
            '--cpus', ','.join(map(str, range(32, 64))), '--memory-gib', '48',
            '--profile-json', str(out/'PROFILES.json'), '--aggregate-gib', '300',
            '--host-reserve-gib', '512']


def controller():
    path = PARENT/'recover_count_v2.py'
    need(sha(path) == COUNT_CONTROLLER, 'immutable original numerical controller')
    sys.path.insert(0, str(PARENT))
    spec = importlib.util.spec_from_file_location('cold_count_original', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def prepare(count, out):
    count, out = count.resolve(), out.resolve()
    need(sha(count/'MANIFEST.json') == COUNT_MANIFEST, 'fixed original count source scope')
    need(not out.exists() and not out.is_relative_to(count) and not out.is_relative_to(ROOT),
         'fresh owned output outside original count and source checkout')
    original = read(count/'MANIFEST.json')
    data = data_inputs(original)
    old_parts = sorted(name for name in original['basis'] if name.startswith(NS+'.Check'))
    need(len(data) == 695 and len(old_parts) == 299, 'exact missing legacy695+299 population')
    need(shutil.disk_usage(out.parent).free >= 1 << 40, 'independent disk admission')
    out.mkdir()
    source = out/'source'
    source.mkdir()
    copied = []
    for name, old in sorted(data.items()):
        receipt = read(old['compiler_receipt'])
        path = Path(receipt['source'])
        need(sha(path) == old['source_sha256'], 'locked untrusted numerical source identity')
        target = source/rel(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        need(sha(target) == old['source_sha256'], 'copied numerical source')
        amount = old['memory_limit_bytes']
        need(type(amount) is int and amount % (1 << 30) == 0, 'recorded source-specific cap')
        copied.append(dict(module=name, path=str(target.relative_to(out)),
                           sha256=old['source_sha256'], original_source=str(path),
                           old_object_sha256=old['object_sha256'],
                           address_cap_GiB=amount >> 30))
    portable = PARENT/'portable'
    frozen = read(portable/'SOURCE_CLOSURE.json')
    application = []
    for row in frozen['modules']:
        path = portable/'source'/row['relative']
        need(sha(path) == row['source_sha256'], 'pinned checker application source')
        target = source/row['relative']
        need(not target.exists(), 'unambiguous numerical/checker source identity')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        application.append(dict(module=row['module'], path=str(target.relative_to(out)),
                                sha256=row['source_sha256']))
    for row in frozen['resources']:
        path = portable/'source'/row['relative']
        need(sha(path) == row['sha256'], 'pinned unused-or-selected C resource')
        target = source/row['relative']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    engine = out/'engine/Solutions/Replay/scripts'
    engine.mkdir(parents=True)
    for row in read(portable/'CONTROLLERS.json')['controllers']:
        path = portable/row['path']
        need(sha(path) == row['sha256'], 'unchanged existing source-only engine')
        shutil.copyfile(path, engine/path.name)
    caps = {row['module']: row['address_cap_GiB'] for row in copied}
    caps['RamanujanPV.SelectedReplayAudit'] = 256
    save(out/'PROFILES.json', dict(exact=caps, prefix={}))
    context = ROOT/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
    command = execution_command(out, context, sys.executable)
    save(out/'PLAN.json', dict(schema='RH_COLD695_DATA_SOURCE_V1', status='PREPARED_NOT_COMPILED',
         numerical_count=str(count), numerical_manifest_sha256=COUNT_MANIFEST,
         controller_sha256=sha(__file__), data=copied, checker_sources=application,
         missing_old_parts=old_parts, context=str(context), context_sha256=sha(context),
         command=command, python_executable=sys.executable,
         python_executable_sha256=sha(Path(sys.executable).resolve()),
         portable_source_manifest_sha256=sha(portable/'SOURCE_CLOSURE.json'),
         profile_sha256=sha(out/'PROFILES.json'),
         historical_application_objects_admitted=False,
         scope='Fresh695 data/gap modules plus actual checker source dependencies. No count or PV completion.'))
    print('PREPARED_COLD695_NO_PROOF_COMPILERS')


def plan_check(out):
    plan = read(out/'PLAN.json')
    need(plan['schema'] == 'RH_COLD695_DATA_SOURCE_V1'
         and plan['controller_sha256'] == sha(__file__), 'cold data controller/source binding')
    need(sha(out/'PROFILES.json') == plan['profile_sha256'], 'exact resource profiles')
    need(len(plan['data']) == 695 and len(plan['missing_old_parts']) == 299, 'complete fixed complement')
    need(sha(Path(plan['numerical_count'])/'MANIFEST.json') == COUNT_MANIFEST,
         'preserved numerical science')
    count = read(Path(plan['numerical_count'])/'MANIFEST.json')
    want = data_inputs(count)
    need([row['module'] for row in plan['data']] == sorted(want), 'all695 exact ordered identities')
    need(plan['missing_old_parts'] == sorted(name for name in count['basis']
         if name.startswith(NS+'.Check')), 'all299 exact original missing proof identities')
    caps = {}
    for row in plan['data']:
        old = want[row['module']]
        need(row['sha256'] == old['source_sha256']
             and row['old_object_sha256'] == old['object_sha256']
             and type(row['address_cap_GiB']) is int
             and row['address_cap_GiB']*(1 << 30) == old['memory_limit_bytes'],
             'canonical data source/object/profile association')
        need(row['path'] == str(Path('source')/rel(row['module'])), 'owned source module path')
        caps[row['module']] = row['address_cap_GiB']
    caps['RamanujanPV.SelectedReplayAudit'] = 256
    need(exact(read(out/'PROFILES.json'), dict(exact=caps, prefix={})), 'exact resource profile values')
    portable = PARENT/'portable'
    need(sha(portable/'SOURCE_CLOSURE.json') == plan['portable_source_manifest_sha256'],
         'checker source capture binding')
    frozen = read(portable/'SOURCE_CLOSURE.json')
    need(exact(plan['checker_sources'], [dict(module=row['module'],
         path=str(Path('source')/row['relative']), sha256=row['source_sha256'])
         for row in frozen['modules']]), 'complete canonical checker source universe')
    for row in read(portable/'CONTROLLERS.json')['controllers']:
        need(sha(out/'engine/Solutions/Replay/scripts'/Path(row['path']).name) == row['sha256'],
             'unchanged executed replay engine')
    context = ROOT/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
    need(plan['context'] == str(context) and plan['context_sha256'] == sha(context),
         'approved source-pinned generic context')
    need(sha(Path(plan['python_executable']).resolve()) == plan['python_executable_sha256'],
         'recorded Python execution identity')
    need(exact(plan['command'], execution_command(out, context, plan['python_executable'])),
         'exact source-only data execution command')
    for row in plan['data']+plan['checker_sources']:
        path = out/row['path']
        need(path.resolve().is_relative_to(out/'source') and path.is_file()
             and not path.is_symlink() and sha(path) == row['sha256'],
             'cold copied source identity')
    for row in frozen['resources']:
        path = out/'source'/row['relative']
        need(path.is_file() and not path.is_symlink() and
             path.resolve().is_relative_to(out/'source') and sha(path) == row['sha256'],
             'all actual C include-string resources preserved')
    return plan


def owned_replay(out, plan, write_probes=False):
    """Strengthen the unchanged engine with exact owned paths and actual imports."""
    context = read(plan['context'])
    import source_basis
    source_basis.validate_generic(context)
    replay = out/'data-replay'
    need(replay.is_dir() and replay.resolve() == replay,
         'owned replay root cannot redirect through an ancestor symlink')
    result, actual = read(replay/'RESULT.json'), read(replay/'PLAN.json')
    engine = out/'engine/Solutions/Replay/scripts/reproduce_profiled_closure.py'
    parser = out/'engine/Solutions/Replay/scripts/rebuild_qrh_closure.py'
    need(sha(replay/'controller.py') == sha(engine) == actual['script_sha256'] and
         sha(replay/'import-parser.py') == sha(parser), 'exact actual replay engine/import parser')
    generic = context['generic_libraries']+[
        str(Path(context['compiler']).parent.parent/'lib/lean')]
    profiles = read(out/'PROFILES.json')
    need(actual['compiler'] == context['compiler'] and
         actual['compiler_sha256'] == context['compiler_sha256'] and
         actual['context'] == plan['context'] and actual['context_sha256'] == plan['context_sha256'] and
         exact(actual['generic_libraries'], generic), 'pinned generic-only execution context')
    policy = dict(targets=[NS+'.GapCheck'], selected_theorems=[NS+'.gaps_checked'],
         old_application_objects_used=False, max_parallel_workers=32,
         aggregate_memory_ceiling_bytes=300 << 30, memory_ceiling_bytes=256 << 30,
         host_reserve_bytes=512 << 30, resource_profile=profiles, default_memory_gib=48,
         final_audit_memory_limit_bytes=256 << 30, cpus=list(range(32, 64)))
    for key, value in policy.items():
        need(exact(actual[key], value), 'exact actually executed data policy:'+key)
    need(type(actual['host_memavailable_before_bytes']) is int and
         actual['host_memavailable_before_bytes'] >= 1 << 40,
         'actual engine high-resource admission')
    captured = {row['module']: row for row in plan['data']+plan['checker_sources']}
    need(len(captured) == len(plan['data'])+len(plan['checker_sources']), 'unique captured source universe')
    C = controller()
    expected, seen, visiting = [], set(), set()
    def visit(name):
        if name in seen:
            return
        if name not in captured:
            need(not name.startswith(('RamanujanPV.', 'LCMSourcePV.', 'RHOcticPush.')) and
                 any((Path(g)/rel(name).with_suffix('.olean')).is_file() for g in generic),
                 'only pinned generic source may be outside captured application')
            return
        need(name not in visiting, 'acyclic exact source import closure')
        visiting.add(name)
        row = captured[name]
        path = out/'source'/rel(name)
        imports = C.imports(path.read_text())
        for imported in imports:
            visit(imported)
        visiting.remove(name)
        seen.add(name)
        expected.append(dict(module=name, root=str(out/'source'), source=str(path),
             source_sha256=row['sha256'], imports=imports,
             memory_limit_bytes=profiles['exact'].get(name, 48) << 30))
    visit(NS+'.GapCheck')
    need(exact(actual['modules'], expected), 'complete actual source-only canonical module closure')
    need(len(result['records']) == len(expected)+1 and
         [q['module'] for q in result['records']] ==
         [q['module'] for q in expected]+['RamanujanPV.SelectedReplayAudit'],
         'exact ordered owned compiler population and generated audit')
    audit_text = 'import '+NS+'.GapCheck\n#print axioms '+NS+'.gaps_checked\n'
    audit_path = replay/'source/RamanujanPV/SelectedReplayAudit.lean'
    need(audit_path.is_file() and not audit_path.is_symlink() and
         audit_path.read_text() == audit_text, 'canonical generated source audit')
    object_map = {}
    for row in result['records']:
        module = row['module']
        audit = module == 'RamanujanPV.SelectedReplayAudit'
        root = replay/'source' if audit else out/'source'
        source = root/rel(module)
        obj = replay/'lean'/rel(module).with_suffix('.olean')
        logs = replay/'audit'/module
        need(row['source'] == str(source) and row['object'] == str(obj) and
             row['command'] == [context['compiler'], '-j1', '-R', str(root), str(source),
                                '-o', str(obj)], 'actual owned source/object/compiler command')
        for key, path in [('source', source), ('object', obj), ('stdout', logs/'stdout'),
                          ('stderr', logs/'stderr'), ('rusage', logs/'rusage')]:
            scope = out/'source' if key == 'source' and not audit else replay
            owned_file(row[key], path, scope, row[key+'_sha256'])
        cap = 256 << 30 if audit else profiles['exact'].get(module, 48) << 30
        need(type(row['exit_code']) is int and row['exit_code'] == 0 and
             row['source_unchanged_during_compile'] is True and
             type(row['memory_limit_bytes']) is int and row['memory_limit_bytes'] == cap and
             row['oom_or_sigkill_event'] is False, 'strict actual source compilation and cap')
        usage = (logs/'rusage').read_text()
        match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
        need(match is not None and type(row['peak_rss_bytes']) is int and
             row['peak_rss_bytes'] == int(match[1])*1024 and
             0 < row['peak_rss_bytes'] <= cap, 'actual owned child peak memory')
        observed_wall(usage, row['seconds'])
        snapshot = logs/'source.lean'
        need(snapshot.is_file() and not snapshot.is_symlink() and
             snapshot.resolve().is_relative_to(replay) and
             snapshot.read_bytes() == source.read_bytes(),
             'actual executed source snapshot matches canonical source')
        object_map[obj.resolve()] = row['object_sha256']
    selected_payloads = {}
    for row in expected:
        source = Path(row['source'])
        for value in re.findall(r'include_str\s+"([^"]+)"', source.read_text()):
            path = (source.parent/value).resolve()
            need(path.is_relative_to(out/'source'), 'owned actual C include-string input')
            selected_payloads[str(path)] = sha(path)
    need(exact(actual['payloads'], [dict(path=k, sha256=v)
         for k, v in sorted(selected_payloads.items())]), 'all actual include-string source inputs')
    probes = []
    for row in result['records']:
        module = row['module']
        root = replay/'source' if module == 'RamanujanPV.SelectedReplayAudit' else out/'source'
        target = replay/'owned-dependencies'/module
        command = [context['compiler'], '--root='+str(root), '--deps', str(root/rel(module))]
        if write_probes:
            target.mkdir(parents=True, exist_ok=True)
            cp = subprocess.run(command, capture_output=True, text=True,
                env=dict(os.environ, LEAN_PATH=':'.join([str(replay/'lean'), *generic])))
            for name, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
                (target/name).write_text(text)
            save(target/'PROBE.json', dict(module=module, command=command,
                 returncode=cp.returncode, stdout_sha256=sha(target/'stdout'),
                 stderr_sha256=sha(target/'stderr')))
        probe = read(target/'PROBE.json')
        need(probe['module'] == module and exact(probe['command'], command) and
             type(probe['returncode']) is int and probe['returncode'] == 0,
             'actual source-only compiler dependency probe')
        for key in ['stdout', 'stderr']:
            need(sha(target/key) == probe[key+'_sha256'], 'actual dependency log bytes')
        imports = [NS+'.GapCheck'] if module == 'RamanujanPV.SelectedReplayAudit' else \
                  next(q['imports'] for q in expected if q['module'] == module)
        required = {(replay/'lean'/rel(name).with_suffix('.olean')).resolve()
                    for name in imports if name in seen}
        dependency_paths((target/'stdout').read_text().splitlines(), object_map, generic, required)
        probes.append(probe)
    need(type(result['seconds']) in [int, float] and math.isfinite(result['seconds']) and
         result['seconds'] >= max(q['seconds'] for q in result['records']) and
         type(result['oom_events']) is int and result['oom_events'] == 0 and
         type(result['actual_peak_worker_rss_bytes']) is int and
         result['actual_peak_worker_rss_bytes'] == max(q['peak_rss_bytes'] for q in result['records']),
         'actual complete duration, OOM and child memory summaries')
    return dict(status='PASS_EXACT_OWNED_SOURCE_ONLY_ENGINE_RECEIPTS',
         dependency_probes=probes, actual_scientific_modules=len(expected),
         historical_application_objects_opened=0)


def verify(out, write_probes=False):
    plan = plan_check(out)
    engine = out/'engine/Solutions/Replay/scripts/reproduce_profiled_closure.py'
    cp = subprocess.run([sys.executable, str(engine), '--check', str(out/'data-replay')],
                        capture_output=True, text=True)
    need(cp.returncode == 0, 'actual existing engine complete source readback')
    result = read(out/'data-replay/RESULT.json')
    owned = owned_replay(out, plan, write_probes)
    records = {row['module']: row for row in result['records']}
    need(len(records) == len(result['records']), 'unique actual compiler identities')
    byte_identical = []
    for row in plan['data']:
        got = records[row['module']]
        need(got['source_sha256'] == row['sha256'], 'source-bound fresh data compilation')
        need(got['object_sha256'] == row['old_object_sha256'],
             'fresh data/gap object must be byte-identical before existing proof reuse')
        byte_identical.append(row['module'])
    need(exact(result['axioms'][NS+'.gaps_checked'], []), 'fresh prime-gap proof empty axioms')
    return dict(status='PASS_FRESH695_DATA_AND_GAPS_BYTE_IDENTICAL',
                controller_sha256=sha(__file__), plan_sha256=sha(out/'PLAN.json'),
                replay_result_sha256=sha(out/'data-replay/RESULT.json'),
                owned_source_execution=owned,
                exact_source_fresh_modules=695, byte_identical_modules=byte_identical,
                no_historical_application_objects=True, missing_old_parts=299,
                scope='Source-fresh data/gaps only.299 old numerical parts, freshFinal and new selected source consumer remain separate.')


def run(out):
    plan = plan_check(out)
    lock = (out/'DATA_STAGE.lock').open('a')
    fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    need(not (out/'DATA_RESULT.json').exists() and not (out/'data-replay').exists(),
         'fresh data compilation attempt; preserve previous attempts')
    old = controller()
    old.validate(Path(plan['numerical_count']))
    need(old.available() >= 812*(1 << 30),
         '512GiB host reserve plus at most300GiB simultaneous owned address caps')
    with (out/'data.stdout').open('w') as stdout, (out/'data.stderr').open('w') as stderr:
        start = time.monotonic()
        cp = subprocess.run(plan['command'], stdout=stdout, stderr=stderr,
                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    save(out/'DATA_EXECUTION.json', dict(command=plan['command'], returncode=cp.returncode,
         seconds=time.monotonic()-start, stdout_sha256=sha(out/'data.stdout'),
         stderr_sha256=sha(out/'data.stderr')))
    need(cp.returncode == 0, 'fresh data phase failure retained without acceptance')
    report = verify(out, write_probes=True)
    save(out/'DATA_RESULT.json', report)
    print(report['status'])


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--count', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    need(sum([args.prepare, args.run, args.verify, args.check]) == 1,
         'one explicit stage operation')
    if args.prepare:
        need(args.count is not None, 'explicit immutable numerical run')
        prepare(args.count, args.out)
    else:
        need(args.count is None, 'count is fixed by prepared plan')
        out = args.out.resolve()
        if args.run:
            run(out)
        elif args.check:
            plan_check(out)
            print('PASS_PREPARED695_CANONICAL_SOURCES_NO_COMPILERS')
        else:
            print(json.dumps(verify(out), sort_keys=True))


if __name__ == '__main__':
    main()
