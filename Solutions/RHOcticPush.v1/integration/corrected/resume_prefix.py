"""Admit only the recorded114-source prefix rejected at the missing C127 harness.

All reused objects were compiled from source in this same new campaign. This
helper does not accept the rejected run, and no old native outputs are reused.
"""
from pathlib import Path
import hashlib, json, math, os, re, shutil, subprocess

HERE = Path(__file__).resolve().parent
I = HERE.parent
R = I.parents[2]
ORIGINAL_PACKET_SHA256 = '58a23b0b25c6eb194cc89e587d8b308878729f8539c6ca89cb246412ecc8f851'


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate prefix JSON key')
            result[key] = value
        return result
    def finite(value):
        number = float(value)
        need(math.isfinite(number), 'nonfinite prefix JSON number')
        return number
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_float=finite,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite prefix JSON')))


def validate_prefix(old, manifest, context, foundation):
    old = Path(old).resolve()
    need((old/'FAILURE.json').is_file() and not (old/'RESULT.json').exists(),
         'only the preserved rejected runtime-stage attempt supplies a prefix')
    watched = ['FAILURE.json', 'BUILD.json', 'RESOURCE_ADMISSION.json',
               'reproduce.executed.py', 'SOURCE_CLOSURE.executed.json',
               'C-log127.stdout', 'C-log127.stderr']
    initial = {name: sha(old/name) for name in watched}
    need(initial['reproduce.executed.py'] == sha(I/'runtime_recovery/ORIGINAL_PRIMARY_CONTROLLER.py'),
         'exact original executed primary controller')
    need(initial['SOURCE_CLOSURE.executed.json'] == sha(I/'corrected/capture/SOURCE_CLOSURE.json'),
         'exact original mathematical source freeze')
    failure = read(old/'FAILURE.json')
    need(failure['error'] == 'stage failed:C-log127'
         and type(failure['completed_modules']) is int and failure['completed_modules'] == 114,
         'precise missing-runtime stage and114 completed modules')
    build = read(old/'BUILD.json')
    need(build['status'] == 'RUNNING' and len(build['modules']) == len(manifest['modules']) == 114,
         'all114 successful compilations before runtime-only failure')
    admission = read(old/'RESOURCE_ADMISSION.json')
    need(type(admission['memory_cap_bytes']) is int
         and admission['memory_cap_bytes'] == 64*(1 << 30)
         and type(admission['host_RAM_reserve_bytes']) is int
         and admission['host_RAM_reserve_bytes'] == 512*(1 << 30),
         'exact original64GiB source lane and512GiB host reserve')
    rejected_native = (old/'C-log127.stderr').read_text()
    missing = re.findall(r"can't open file '([^']+)'", rejected_native)
    need(len(missing) == 1 and missing[0].endswith(
        '/Solutions/RHContinuation.v1/parabolic/native_log_workload.py')
        and 'Exit status: 2' in rejected_native, 'actual missing Python runtime harness failure')
    missing_path = Path(missing[0])
    need(not missing_path.exists() and sha(missing_path.parents[3].parent/'SOURCE_PACKET.json')
         == ORIGINAL_PACKET_SHA256, 'unchanged original compact packet missing the runtime file')
    need(not (old/'C-log127').exists() and not (old/'C-ram').exists(),
         'no old native execution artifacts are reused')
    original = read(old/'SOURCE_CLOSURE.executed.json')
    need(original == manifest, 'identical full114 source manifest')
    for resource in manifest['resources']:
        path = old/'source'/resource['relative_runtime_path']
        need(path.is_file() and not path.is_symlink() and sha(path) == resource['sha256'],
             'actual old runtime include resource identity')
    maps, prefix, probes = dict(foundation), [], []
    generic = [Path(path).resolve() for path in context['generic_libraries']]
    generic.append(Path(context['compiler']).resolve().parent.parent/'lib/lean')
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    environment['LEAN_PATH'] = os.pathsep.join([str(old/'union'), *context['generic_libraries']])
    for want, row in zip(manifest['modules'], build['modules']):
        module = want['module']
        relative = module.replace('.', '/')
        source, obj = old/'source'/(relative+'.lean'), old/'objects'/(relative+'.olean')
        need(row['module'] == module and type(row['returncode']) is int and row['returncode'] == 0,
             'contiguous actual successful compiler prefix')
        need(module not in maps and set(want['application_imports']) <= set(maps),
             'ordered exact prefix import closure')
        need(source.is_file() and obj.is_file() and not source.is_symlink() and not obj.is_symlink()
             and source.resolve().is_relative_to(old/'source')
             and obj.resolve().is_relative_to(old/'objects'), 'owned regular prefix source/object')
        need(sha(source) == want['sha256'] == row['source_sha256']
             and sha(obj) == row['object_sha256'], 'exact prefix source/object hashes')
        expected = ['/usr/bin/time', '-v', context['compiler'], '--root='+str(old/'source'),
                    '-j4', '-o', str(obj), str(source)]
        need(type(row['seconds']) in [int, float] and math.isfinite(row['seconds'])
             and row['seconds'] >= 0 and type(row['peak_RSS_KiB']) is int
             and row['peak_RSS_KiB'] >= 0, 'actual finite prefix resource measurements')
        for suffix in ['stdout', 'stderr']:
            need(sha(old/'logs'/(module+'.'+suffix)) == row[suffix+'_sha256'], 'prefix compiler log')
        stderr = (old/'logs'/(module+'.stderr')).read_text()
        rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', stderr)
        need(rss is not None and int(rss[1]) == row['peak_RSS_KiB']
             and 'Exit status: 0' in stderr, 'actual original GNU compiler success/RSS')
        elapsed = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)', stderr)
        need(elapsed is not None and len(elapsed[1].split(':')) in [2, 3],
             'actual original GNU compiler elapsed time')
        actual_seconds = 0.0
        for field in elapsed[1].split(':'):
            actual_seconds = 60*actual_seconds+float(field)
        need(math.isfinite(actual_seconds) and actual_seconds >= 0
             and actual_seconds <= row['seconds']+1 and row['seconds'] <= actual_seconds+5,
             'prefix compiler duration against actual GNU time')
        need(row['command'] == expected, 'exact original compiler command')
        timed = re.findall(r'Command being timed: "([^\n]+)"', stderr)
        need(timed == [' '.join(expected[2:])], 'actual GNU timed compiler command association')
        command = [context['compiler'], '--root='+str(old/'source'), '--deps', str(source)]
        process = subprocess.run(command, cwd=old/'source', env=environment,
                                 capture_output=True, text=True)
        need(process.returncode == 0 and process.stdout.strip(), 'actual nonempty prefix dependency probe')
        direct = set()
        for line in process.stdout.splitlines():
            path = Path(line).resolve()
            if any(path.is_relative_to(bank) for bank in generic):
                continue
            identities = [(name, item) for name, item in maps.items()
                          if item['object'].resolve() == path]
            need(len(identities) == 1 and sha(path) == identities[0][1]['object_sha256'],
                 'no foreign or changed application dependency in reused prefix')
            direct.add(identities[0][0])
        need(set(want['application_imports']) <= direct, 'every actual direct prefix application import')
        probes.append({'module': module, 'command': command, 'returncode': process.returncode,
            'stdout': process.stdout, 'stderr': process.stderr,
            'stdout_sha256': hashlib.sha256(process.stdout.encode()).hexdigest(),
            'stderr_sha256': hashlib.sha256(process.stderr.encode()).hexdigest()})
        maps[module] = {'object': obj, 'object_sha256': row['object_sha256']}
        prefix.append(row)
    need(len(prefix) == 114, 'complete114 source-fresh prefix only')
    need(all(sha(old/name) == value for name, value in initial.items()),
         'original rejected evidence unchanged during admission')
    receipt = {'root': str(old), 'rejected_BUILD_sha256': initial['BUILD.json'],
        'rejected_FAILURE_sha256': initial['FAILURE.json'],
        'original_controller_sha256': initial['reproduce.executed.py'],
        'original_manifest_sha256': initial['SOURCE_CLOSURE.executed.json'],
        'original_compact_packet_sha256': ORIGINAL_PACKET_SHA256,
        'prefix_count': 114, 'prefix_compiler_seconds': sum(row['seconds'] for row in prefix),
        'first_recompiled_module': None, 'prefix_dependency_probes': probes,
        'original_failure_kind': 'missing compact runtime harness after114 successful same-campaign '
            'source compilations; not an OOM or mathematical proof failure',
        'native_outputs_reused': False, 'uninterrupted_run_claim': False}
    return receipt, prefix


def copy_prefix(old, out, rows, union, maps):
    for row in rows:
        module = row['module']
        relative = module.replace('.', '/')
        for directory, suffix in [('source', '.lean'), ('objects', '.olean')]:
            target = out/directory/(relative+suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(old/directory/(relative+suffix), target)
        for suffix in ['stdout', 'stderr']:
            shutil.copyfile(old/'logs'/(module+'.'+suffix), out/'logs'/(module+'.'+suffix))
        obj = out/'objects'/(relative+'.olean')
        target = union/(relative+'.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        need(not target.exists(), 'prefix namespace collision')
        target.symlink_to(obj)
        maps[module] = {'object': obj, 'object_sha256': row['object_sha256']}
    return list(rows)
