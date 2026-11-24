#!/usr/bin/env python3
"""Append the four fixed IEANTN-consumer sources to an accepted cold305 run.

Use --basis ACCEPTED305 --context GENERIC_CONTEXT.json --out FRESH_OUTPUT.
Use --verify OUTPUT for a complete readback. No proof compilation is performed
by --verify. The cold305 reader and its generic/source provenance stay in force.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import math
import os
import re
import shutil
import stat
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
CLOSURE_SHA = '4bc3cf81a5688cfbe9ad87f3665c1995706f7c8e59be34f887bbe11f2d75e13f'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
SMALL_MEMORY = 32 << 30
FULL_MEMORY = 256 << 30
THREADS = 2
STATUS = 'PASS_FRESH_SAME_RUN_SOURCE_BYTES_TO_EXISTING_IEANTN_PI'
TARGET = 'RHOcticPush.IEANTNCount.'
REQUIRED = ['RHOcticPush.ColdCount.complete_actual_source_run',
    'RHOcticPush.SourceOutputAdapter.canonical_source_output',
    'RHOcticPush.CounterSyntax.complete_canonical_source_run',
    'RHOcticPush.CounterSyntax.possible_source_success',
    'RHOcticPush.CounterSyntax.checkedCounter_sound',
    'RHOcticPush.CounterSyntax.checkedDriver_sound',
    'RHOcticPush.HighDriverRuntime.successful_main_output',
    'RamanujanPV.QuotientCFunction.completed_execution_correct',
    'RamanujanPV.HighTransitionCount.pi_1490000000000', TARGET+'wordBytes_injective_below']


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
            need(key not in result, 'duplicate append JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
        parse_float=lambda x: finite(x),
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite append JSON')))


def finite(value):
    result = float(value)
    need(math.isfinite(result), 'nonfinite append JSON number')
    return result


def save(path, value):
    path = Path(path)
    pending = path.with_name('.'+path.name+'.pending')
    need(not pending.exists(), 'fresh atomic append receipt temporary')
    pending.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(pending, path)


def regular(path, message):
    path = Path(path)
    need(stat.S_ISREG(path.lstat().st_mode) and not path.is_symlink(), message)


def owned_regular(root, path):
    root, path = Path(root).resolve(), Path(path)
    label = str(path.relative_to(root))
    regular(path, 'owned regular nonsymlink artifact:'+label)
    need(path.resolve().is_relative_to(root) and
         all(not parent.is_symlink() for parent in path.parents if parent.is_relative_to(root)),
         'owned regular nonsymlink artifact:'+label)


def closure():
    need(sha(HERE/'SOURCE_CLOSURE.json') == CLOSURE_SHA, 'reviewed four-source closure')
    manifest = read(HERE/'SOURCE_CLOSURE.json')
    need(sha(HERE/'RESOURCE_POLICY.json') == manifest['resource_policy_sha256'],
         'reviewed module resource policy')
    need([r['module'] for r in manifest['files']] == ['IEANTN.Vocabulary.PrimeCounting',
        'WordBytesBounded', 'IEANTNCountConsumer', 'IEANTNCountConsumerAudit'], 'exact four-source order')
    for row in manifest['files']:
        source = ROOT/row['source']
        need(source.is_file() and not source.is_symlink() and sha(source) == row['sha256'],
             'reviewed current source bytes:'+row['module'])
    provider = HERE.parent/'cold-foundation'
    for row in manifest['providers']:
        need(sha(provider/row['file']) == row['sha256'], 'unchanged accepted305 provider:'+row['file'])
    portable = HERE.parent/'portable-source-run'
    for name, digest in manifest['portable_basis_pins'].items():
        need(sha(portable/name) == digest, 'unchanged clean portable basis reader:'+name)
    sys.path.insert(0, str(provider))
    spec = importlib.util.spec_from_file_location('ieantn_accepted305', provider/'remaining_stage.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return manifest, module


def cold_basis(path, context, cold):
    path = Path(path).resolve()
    before = {name: sha(path/name) for name in ['PLAN.json', 'RESULT.json']}
    original_basis = cold.basis
    captured = []

    def observe(plan):
        need(not captured, 'one original cold basis invocation')
        need(cold.exact(plan, read(path/'PLAN.json')), 'observer uses the same exact cold plan')
        value = original_basis(plan)
        need(type(value) is tuple and len(value) == 4 and type(value[0]) is dict,
             'original validated cold basis tuple')
        captured.append((plan, value))
        return value

    cold.basis = observe
    try:
        result = cold.validate(path)
    finally:
        cold.basis = original_basis
    need(cold.basis is original_basis and len(captured) == 1 and
         before == {name: sha(path/name) for name in before} and
         cold.exact(result, read(path/'RESULT.json')), 'one complete unchanged frozen cold validation')
    plan, (maps, _collisions, expected, _provenance) = captured[0]
    need(len(result['records']) == len(plan['modules']) == 305, 'all305 actual validated records')
    for row, record in zip(plan['modules'], result['records']):
        actual = maps[row['module']]
        need(actual['source_sha256'] == row['sha256'] and
             actual['object_sha256'] == record['object_sha256'] and
             Path(actual['object']).resolve() ==
             (path/'objects'/cold.rel(row['module']).with_suffix('.olean')).resolve(),
             'same returned map extended by full305 validation')
    keys = ['compiler', 'compiler_sha256', 'generic_libraries', 'generic_dependencies']
    need(cold.exact({key: context[key] for key in keys}, {key: expected[key] for key in keys}),
         'same validated generic-only context')
    cold.B.validate_generic(context)
    return {name: dict(item) for name, item in maps.items()}, dict(kind='cold305', root=str(path),
        RESULT_sha256=before['RESULT.json'], controller_sha256=sha(Path(cold.__file__)),
        modules=len(maps), original_validate_invocations=1, observed_original_basis_invocations=1)


def portable_basis(path, context, cold):
    path = Path(path).resolve()
    before = {name: sha(path/name) for name in ['PLAN.json', 'RESULT.json', 'replay/RESULT.json']}
    reader = HERE.parent/'portable-source-run/readback.py'
    spec = importlib.util.spec_from_file_location('ieantn_portable_full_basis', reader)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    checked = module.verify(path, write_probes=False, candidate=False)
    need(checked['status'] == 'PASS_FULL_CLEAN_PHYSICAL_COUNT_AND_SOURCE_RUN' and
         checked['fixed_high_output_proved'] is True and
         checked['exact_mathematical_target'] == [1490000000000, 55206486339],
         'accepted full-high portable basis required; smoke is not the fixed high result')
    plan = read(path/'PLAN.json')
    need(plan['smoke'] is False and before == {name: sha(path/name) for name in before},
         'one unchanged full clean portable basis')
    expected = read(plan['context'])
    keys = ['compiler', 'compiler_sha256', 'generic_libraries', 'generic_dependencies']
    need(cold.exact({key: context[key] for key in keys}, {key: expected[key] for key in keys}),
         'same validated clean portable generic context')
    cold.B.validate_generic(context)
    records = read(path/'replay/RESULT.json')['records']
    maps = {}
    for row in records:
        name = row['module']
        need(name not in maps, 'unique fully checked portable compiler identity')
        maps[name] = dict(source_sha256=row['source_sha256'], object=row['object'],
                          object_sha256=row['object_sha256'])
    need(all(name in maps for name in ['CountSourceFinal', 'CountSourceAudit', 'CounterSyntaxAudit']),
         'full portable source-facing closure endpoints')
    return maps, dict(kind='portable-full', root=str(path), RESULT_sha256=before['RESULT.json'],
        replay_RESULT_sha256=before['replay/RESULT.json'], reader_sha256=sha(reader), modules=len(maps))


def basis(path, context, cold, kind):
    need(kind in ['cold305', 'portable-full'], 'explicit supported accepted basis kind')
    maps, provenance = cold_basis(path, context, cold) if kind == 'cold305' else portable_basis(path, context, cold)
    manifest = read(HERE/'SOURCE_CLOSURE.json')
    rebuilt = []
    for row in manifest['files']:
        if row['module'] in maps:
            need(maps[row['module']]['source_sha256'] == row['sha256'],
                 'identical source for freshly rebuilt vocabulary collision')
            rebuilt.append(dict(module=row['module'], source_sha256=row['sha256'],
                                prior_object_sha256=maps[row['module']]['object_sha256']))
            del maps[row['module']]
    provenance['identical_sources_rebuilt_fresh'] = rebuilt
    return maps, provenance


def relative(module):
    return Path(module.replace('.', '/')+'.lean')


def profile(module):
    return (SMALL_MEMORY, 120) if module in ['IEANTN.Vocabulary.PrimeCounting', 'WordBytesBounded'] else (FULL_MEMORY, 1800)


def command(compiler, root, module):
    memory, timeout = profile(module)
    return ['/usr/bin/timeout', '--signal=TERM', '--kill-after=5s', str(timeout)+'s',
        '/usr/bin/prlimit', '--as='+str(memory), '--', '/usr/bin/time', '-v',
        '-o', str(root/'logs'/(module+'.resources')), compiler, '--root='+str(root/'source'),
        '-j'+str(THREADS), '-o', str(root/'objects'/relative(module).with_suffix('.olean')),
        str(root/'source'/relative(module))]


def wall(text):
    found = re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', text)
    need(len(found) == 1 and len(found[0].split(':')) in [2, 3], 'one actual GNU elapsed time')
    return sum(float(x)*60**i for i, x in enumerate(reversed(found[0].split(':'))))


def axioms(text, expected):
    rows = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", text, re.M)
    need(len(rows) == len(expected) and {x[0] for x in rows} == set(expected), 'exact printed theorem roots')
    result = {}
    for name, names in rows:
        values = [x.strip() for x in names.split(',') if x.strip()]
        need(len(values) == len(set(values)) and set(values) <= STD, 'standard theorem axioms only')
        result[name] = values
    return result


def audit(text, cold):
    def payloads(marker):
        return [cold.payload(line.split(marker, 1)[1]) for line in text.splitlines() if marker+'{' in line]
    rows = payloads('IEANTN_COUNT_AXIOMS ')
    names = {TARGET+x for x in ['wordBytes_injective_below', 'fixed_count_from_same_source_run',
                              'primeCounting_fixed_point']}
    need(len(rows) == 3 and {x['name'] for x in rows} == names, 'all three unique actual axiom audit rows')
    for row in rows:
        need(set(row) == {'name', 'axioms'} and type(row['axioms']) is list and
             all(type(x) is str and x in STD for x in row['axioms']) and
             len(row['axioms']) == len(set(row['axioms'])), 'strict standard audit axiom rows')
    values = payloads('IEANTN_COUNT_VALUE_PATH ')
    need(len(values) == 1, 'one actual IEANTN VALUE payload')
    value = values[0]
    need(set(value) == {'root', 'required', 'checked_edges', 'IEANTN_object_in_checked_type', 'exact_target_checked',
         'numerical_witness', 'physical_trace_claim'} and
         value['root'] == TARGET+'primeCounting_fixed_point' and value['required'] == REQUIRED and
         type(value['checked_edges']) is int and value['checked_edges'] == 33 and
         value['IEANTN_object_in_checked_type'] is True and value['exact_target_checked'] is True and
         value['physical_trace_claim'] is False and
         value['numerical_witness'] == 'Existing exhaustive kernel count; no new native verification',
         'complete exact same-run/grammar/correctness/byte VALUE audit')
    need(text.count('IEANTN_COUNT_EXACT_TYPE ') == 1, 'one actual IEANTN theorem type audit')
    return dict(axioms=rows, value=value)


def probe(root, context, row, maps, write=False):
    module = row['module']
    cmd = [context['compiler'], '--root='+str(root/'source'), '--deps', str(root/'source'/relative(module))]
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1',
        LEAN_PATH=os.pathsep.join([str(root/'union'), *context['generic_libraries']]))
    cp = subprocess.run(cmd, cwd=root/'source', env=env, capture_output=True, text=True, timeout=120)
    need(cp.returncode == 0 and cp.stdout.strip(), 'nonempty actual direct dependency probe')
    generic = [Path(x).resolve() for x in context['generic_libraries']]
    generic.append(Path(context['compiler']).resolve().parent.parent/'lib/lean')
    allowed = {Path(x['object']).resolve(): x['object_sha256'] for x in maps.values()}
    seen = set()
    for line in cp.stdout.splitlines():
        need(line and line.strip() == line, 'canonical actual dependency pathname')
        path = Path(line).resolve()
        seen.add(path)
        if path in allowed:
            need(sha(path) == allowed[path], 'unchanged actual application dependency')
        else:
            banks = [g for g in generic if path.is_relative_to(g)]
            need(banks and not any(part in {'IEANTN', 'RamanujanPV', 'LCMSourcePV', 'RHOcticPush'}
                 for part in path.relative_to(banks[0]).parts), 'no foreign/generic-disguised application dependency')
    need(all(Path(maps[name]['object']).resolve() in seen for name in row['application_imports']),
         'every actual direct application import')
    record = dict(command=cmd, returncode=cp.returncode)
    for suffix, data in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
        path = root/'dependencies'/(module+'.'+suffix)
        if write:
            path.write_text(data)
        owned_regular(root, path)
        need(path.read_text() == data, 'same actual dependency output')
        record[suffix+'_sha256'] = sha(path)
    return record


def validate(root, candidate=None):
    root = Path(root).resolve()
    manifest, cold = closure()
    for path in [candidate or root/'RESULT.json', root/'reproduce.executed.py',
                 root/'SOURCE_CLOSURE.executed.json', root/'GENERIC_CONTEXT.executed.json',
                 root/'RESOURCE_ADMISSION.json']:
        owned_regular(root, path)
    result = read(candidate or root/'RESULT.json')
    need(result['status'] == STATUS and result['controller_sha256'] == sha(__file__) ==
         sha(root/'reproduce.executed.py') and result['closure_sha256'] == CLOSURE_SHA ==
         sha(root/'SOURCE_CLOSURE.executed.json'), 'accepted controller and source closure identity')
    context = read(root/'GENERIC_CONTEXT.executed.json')
    need(sha(root/'GENERIC_CONTEXT.executed.json') == result['context_sha256'], 'captured generic context')
    need([r['module'] for r in result['compilations']] == [r['module'] for r in manifest['files']],
         'all four actual compilation routes')
    for row, got in zip(manifest['files'], result['compilations']):
        module = row['module']
        src, obj = root/'source'/relative(module), root/'objects'/relative(module).with_suffix('.olean')
        owned_regular(root, src)
        owned_regular(root, obj)
        need(src.is_file() and obj.is_file() and not src.is_symlink() and not obj.is_symlink() and
             sha(src) == got['source_sha256'] == row['sha256'], 'frozen append source:'+module)
        need(sha(obj) == got['object_sha256'], 'owned append object:'+module)
        need(type(got['returncode']) is int and got['returncode'] == 0, 'actual compiler success')
        need(got['command'] == command(context['compiler'], Path(result['execution_root']), module),
             'exact executed compiler command')
        for suffix in ['stdout', 'stderr', 'resources']:
            owned_regular(root, root/'logs'/(module+'.'+suffix))
            need(sha(root/'logs'/(module+'.'+suffix)) == got[suffix+'_sha256'], 'actual compiler log bytes')
        for suffix in ['stdout', 'stderr']:
            path = root/'dependencies'/(module+'.'+suffix)
            owned_regular(root, path)
            need(sha(path) == got['dependency_probe'][suffix+'_sha256'], 'actual dependency log bytes')
        usage = (root/'logs'/(module+'.resources')).read_text()
        argv = got['command']
        timed_index = argv.index('/usr/bin/time')
        timed = re.findall(r'Command being timed: "([^\n]+)"', usage)
        need(timed == [' '.join(argv[timed_index+4:])], 'actual GNU timed compiler argv')
        need('Exit status: 0' in usage and type(got['seconds']) in [int, float] and
             math.isfinite(got['seconds']) and got['seconds'] == wall(usage), 'actual successful GNU elapsed')
        rss = re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
        need(len(rss) == 1 and type(got['peak_RSS_KiB']) is int and
             0 < got['peak_RSS_KiB'] == int(rss[0]) <= profile(module)[0]//1024,
             'actual bounded child RSS')
        need(type(got['MemAvailable_before_bytes']) is int and
             got['MemAvailable_before_bytes'] >= (512 << 30)+profile(module)[0],
             'each compiler admission preserves host reserve')
        text = (root/'logs'/(module+'.stdout')).read_text()
        need(not any(x in text+(root/'logs'/(module+'.stderr')).read_text()
                     for x in ['sorryAx', 'Lean.ofReduceBool', 'declaration uses `sorry`']), 'no proof admits/native axiom')
        need(got['axioms'] == axioms(text, row['axiom_roots']), 'actual standard theorem axioms')
    actual_audit = audit((root/'logs/IEANTNCountConsumerAudit.stdout').read_text(), cold)
    need(cold.exact(actual_audit, result['audit']), 'same actual compiler VALUE/axiom audit')
    need(result['execution_root'] == str(root), 'read back at the recorded owned execution root')
    for directory, suffix in [('source', '.lean'), ('objects', '.olean')]:
        entries = list((root/directory).rglob('*'))
        need(not any(p.is_symlink() for p in entries) and
             {str(p.relative_to(root/directory)) for p in entries if p.is_file()} ==
             {str(relative(r['module']).with_suffix(suffix)) for r in manifest['files']},
             'exact owned four-source/object inventory')
    admission = read(root/'RESOURCE_ADMISSION.json')
    need(sha(root/'RESOURCE_ADMISSION.json') == result['admission_sha256'] and
         set(admission) == {'MemAvailable_bytes', 'host_reserve_bytes', 'small_AS_bytes', 'full_AS_bytes',
                           'threads', 'small_timeout_seconds', 'full_timeout_seconds', 'free_disk_bytes'} and
         all(type(v) is int for v in admission.values()) and
         admission['host_reserve_bytes'] == 512 << 30 and admission['small_AS_bytes'] == SMALL_MEMORY and
         admission['full_AS_bytes'] == FULL_MEMORY and admission['threads'] == THREADS and
         admission['small_timeout_seconds'] == 120 and admission['full_timeout_seconds'] == 1800 and
         admission['MemAvailable_bytes'] >= (512 << 30)+FULL_MEMORY and
         admission['free_disk_bytes'] >= 10 << 30, 'actual bounded resource admission')
    maps, foundation = basis(result['basis']['root'], context, cold, result['basis']['kind'])
    need(cold.exact(foundation, result['basis']), 'unchanged fully accepted305 source-built basis')
    for row, got in zip(manifest['files'], result['compilations']):
        need(cold.exact(probe(root, context, row, maps), got['dependency_probe']),
             'actual direct dependency readback')
        maps[row['module']] = dict(object=str(root/'objects'/relative(row['module']).with_suffix('.olean')),
                                  object_sha256=got['object_sha256'])
    union = [p for p in (root/'union').rglob('*') if not p.is_dir()]
    need({str(p.relative_to(root/'union')) for p in union} ==
         {str(relative(name).with_suffix('.olean')) for name in maps} and
         all(p.is_symlink() and p.resolve() == Path(maps[str(p.relative_to(root/'union'))[:-6]
             .replace('/', '.')]['object']).resolve() for p in union), 'exact validated application union')
    need(result['new_numerical_point'] is False and result['full_Ramanujan_finite_coverage'] is False and
         result['new_native_verification'] is False and result['physical_trace_claim'] is False and
         result['DEV_objects_used'] is False, 'precise selected source/real-object scope')
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--basis', type=Path)
    parser.add_argument('--basis-kind', choices=['cold305', 'portable-full'])
    parser.add_argument('--context', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        need(args.basis is None and args.basis_kind is None and args.context is None and args.out is None,
             'exclusive readback route')
        validate(args.verify)
        print('PASS_IEANTN_SAME_RUN_BYTE_CONSUMER_READBACK')
        return
    need(args.basis is not None and args.context is not None and args.out is not None, 'basis/context/out required')
    manifest, cold = closure()
    regular(args.context, 'regular nonsymlink pinned generic context')
    context = read(args.context)
    maps, foundation = basis(args.basis, context, cold, args.basis_kind or 'cold305')
    out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(ROOT) and
         not out.is_relative_to(args.basis.resolve()), 'fresh separate owned append directory')
    available = next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= (512 << 30)+FULL_MEMORY, 'host512GiB reserve plus256GiB full-consumer cap')
    free_disk = shutil.disk_usage(out.parent).free
    need(free_disk >= 10 << 30, 'independent10GiB free disk admission')
    out.mkdir()
    for name in ['source', 'objects', 'union', 'logs', 'dependencies']:
        (out/name).mkdir()
    shutil.copyfile(__file__, out/'reproduce.executed.py')
    shutil.copyfile(HERE/'SOURCE_CLOSURE.json', out/'SOURCE_CLOSURE.executed.json')
    shutil.copyfile(args.context, out/'GENERIC_CONTEXT.executed.json')
    save(out/'RESOURCE_ADMISSION.json', dict(MemAvailable_bytes=available,
        host_reserve_bytes=512 << 30, small_AS_bytes=SMALL_MEMORY, full_AS_bytes=FULL_MEMORY,
        threads=THREADS, small_timeout_seconds=120, full_timeout_seconds=1800, free_disk_bytes=free_disk))
    for name, item in maps.items():
        link = out/'union'/relative(name).with_suffix('.olean')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(item['object'])
    rows = []
    for row in manifest['files']:
        module = row['module']
        source, obj = out/'source'/relative(module), out/'objects'/relative(module).with_suffix('.olean')
        source.parent.mkdir(parents=True, exist_ok=True)
        obj.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/row['source'], source)
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1',
            LEAN_PATH=os.pathsep.join([str(out/'union'), *context['generic_libraries']]))
        cmd = command(context['compiler'], out, module)
        current_available = next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
                                 if x.startswith('MemAvailable:'))
        need(current_available >= (512 << 30)+profile(module)[0], 'host reserve before actual compiler')
        with (out/'logs'/(module+'.stdout')).open('w') as so, (out/'logs'/(module+'.stderr')).open('w') as se:
            cp = subprocess.run(cmd, cwd=out/'source', env=env, stdout=so, stderr=se)
        need(cp.returncode == 0, 'actual append compiler failure preserved:'+module)
        usage = (out/'logs'/(module+'.resources')).read_text()
        record = dict(module=module, command=cmd, returncode=cp.returncode, source_sha256=sha(source),
            object_sha256=sha(obj), seconds=wall(usage),
            peak_RSS_KiB=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)[1]),
            MemAvailable_before_bytes=current_available,
            axioms=axioms((out/'logs'/(module+'.stdout')).read_text(), row['axiom_roots']))
        for suffix in ['stdout', 'stderr', 'resources']:
            record[suffix+'_sha256'] = sha(out/'logs'/(module+'.'+suffix))
        record['dependency_probe'] = probe(out, context, row, maps, write=True)
        link = out/'union'/relative(module).with_suffix('.olean')
        need(not link.exists(), 'new module namespace collision')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(obj)
        maps[module] = dict(object=str(obj), object_sha256=record['object_sha256'])
        rows.append(record)
        save(out/'BUILD.json', rows)
    result = dict(status=STATUS, execution_root=str(out), controller_sha256=sha(__file__),
        closure_sha256=CLOSURE_SHA, context_sha256=sha(out/'GENERIC_CONTEXT.executed.json'), basis=foundation,
        admission_sha256=sha(out/'RESOURCE_ADMISSION.json'),
        compilations=rows, audit=audit((out/'logs/IEANTNCountConsumerAudit.stdout').read_text(), cold),
        new_numerical_point=False, full_Ramanujan_finite_coverage=False,
        new_native_verification=False, physical_trace_claim=False, DEV_objects_used=False)
    save(out/'CANDIDATE.json', result)
    validate(out, out/'CANDIDATE.json')
    os.replace(out/'CANDIDATE.json', out/'RESULT.json')
    print(STATUS)


if __name__ == '__main__':
    main()
