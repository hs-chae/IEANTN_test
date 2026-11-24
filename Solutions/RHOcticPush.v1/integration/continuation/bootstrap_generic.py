#!/usr/bin/env python3
"""Install pinned generic dependencies in a fresh owned checkout.

This downloads only the nine generic Git repositories and official Mathlib
build caches. It never imports or copies an IEANTN application object bank.
The compiler is explicitly provided and checked against the frozen reference.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def save(path, value):
    pending = path.with_name('.'+path.name+'.pending')
    need(not pending.exists(), 'pending receipt collision')
    pending.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(pending, path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cpu', type=int, required=True)
    args = parser.parse_args()
    controller_sha256 = sha(__file__)
    out, compiler = args.out.resolve(), args.compiler.resolve()
    reference = read(REPO/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
    manifest = read(REPO/'lake-manifest.json')
    packages = manifest['packages']
    need([(p['name'], p['rev']) for p in packages] ==
         [(p['name'], p['revision']) for p in reference['generic_dependencies']],
         'exact ordered nine generic source pins')
    need(len(packages) == 9 and len({p['name'] for p in packages}) == 9,
         'unique generic packages')
    need(compiler.is_file() and sha(compiler) == reference['compiler_sha256'],
         'pinned compiler executable')
    lake = compiler.with_name('lake')
    need(lake.is_file(), 'Lake from the same pinned compiler installation')
    need(not out.exists() and not out.is_relative_to(REPO), 'fresh external owned setup root')
    need(args.cpu in os.sched_getaffinity(0), 'one available setup CPU')
    available = next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= 576*(1 << 30), '512GiB host reserve plus64GiB setup allowance')
    need(shutil.disk_usage(out.parent).free >= 1 << 40, 'independent1TiB free disk admission')
    out.mkdir(parents=True)
    logs = out/'logs'
    logs.mkdir()
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('IEANTN_GENERIC_CONTEXT', None)
    env['PATH'] = str(compiler.parent)+os.pathsep+env.get('PATH', '')
    env['MATHLIB_CACHE_DIR'] = str(out/'download-cache')
    env['LEAN_NUM_THREADS'] = '1'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    stages = []
    started = time.monotonic()
    save(out/'PLAN.json', {'schema': 'RH_GENERIC_SETUP_V1', 'controller_sha256': controller_sha256,
         'compiler': str(compiler), 'compiler_sha256': sha(compiler), 'lake_sha256': sha(lake),
         'source_pins': packages, 'cpu': args.cpu, 'MemAvailable_bytes': available,
         'host_reserve_bytes': 512 << 30, 'per_process_address_cap_bytes': 64 << 30,
         'scratch_cap_bytes': 300 << 30, 'application_objects_used': False})

    def run(label, command, cwd):
        wrapped = ['/usr/bin/taskset', '-c', str(args.cpu), '/usr/bin/prlimit',
                   '--as='+str(64 << 30), '--', '/usr/bin/time', '-v', *command]
        stdout, stderr = logs/(label+'.stdout'), logs/(label+'.stderr')
        before = time.monotonic()
        with stdout.open('w') as so, stderr.open('w') as se:
            result = subprocess.run(wrapped, cwd=cwd, env=env, stdout=so, stderr=se)
        row = {'label': label, 'command': wrapped, 'cwd': str(cwd),
               'returncode': result.returncode, 'seconds': time.monotonic()-before,
               'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)}
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', stderr.read_text())
        if match is not None:
            row['peak_child_RSS_KiB'] = int(match[1])
        stages.append(row)
        save(out/'STAGES.json', stages)
        need(result.returncode == 0, 'generic setup stage failed:'+label)
        print(label, round(row['seconds'], 3), flush=True)

    try:
        root = out/'mathlib'
        paths = {}
        for package in packages:
            name = package['name']
            need(re.fullmatch('[A-Za-z][A-Za-z0-9_-]*', name) is not None,
                 'safe literal package name')
            need(package['type'] == 'git' and package['subDir'] is None
                 and package['url'].startswith('https://github.com/'),
                 'pinned public generic Git source')
            path = root if name == 'mathlib' else root/'.lake/packages'/name
            path.parent.mkdir(parents=True, exist_ok=True)
            run(name+'-init', ['git', 'init', '--quiet', str(path)], out)
            run(name+'-remote', ['git', 'remote', 'add', 'origin', package['url']], path)
            run(name+'-fetch', ['git', 'fetch', '--depth', '1', 'origin', package['rev']], path)
            run(name+'-checkout', ['git', 'checkout', '--quiet', '--detach', 'FETCH_HEAD'], path)
            paths[name] = path
        # The pinned package's own cache tool fixes the artifact hash universe.
        # No application source or application cache is present in this checkout.
        run('official-mathlib-cache', [str(lake), 'exe', 'cache', 'get'], root)
        dependencies = []
        for package, expected in zip(packages, reference['generic_dependencies']):
            path = paths[package['name']]
            revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path,
                                               text=True).strip()
            need(revision == package['rev'], 'actual generic Git revision')
            need(subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=path).returncode == 0,
                 'unchanged generic tracked sources')
            library = path/'.lake/build/lib/lean'
            present = library.is_dir()
            need(present or expected['library_present'] is False,
                 'required generic library installed:'+package['name'])
            dependencies.append({'name': package['name'], 'path': str(path),
                'revision': revision, 'url': package['url'], 'library': str(library),
                'tracked_source_clean': True, 'library_present': present})
        context = dict(reference)
        context['compiler'] = str(compiler)
        context['generic_dependencies'] = dependencies
        context['generic_libraries'] = [p['library'] for p in dependencies if p['library_present']]
        context['source_root'] = None
        context['new_application_object_root'] = None
        context['reused_application_proof_objects'] = False
        context['purpose'] = 'Clean generic dependency setup only; no IEANTN application objects'
        context['generic_setup_controller_sha256'] = controller_sha256
        save(out/'GENERIC_CONTEXT.json', context)
        env['LEAN_PATH'] = os.pathsep.join(context['generic_libraries'])
        probe = out/'GenericImport.lean'
        probe.write_text('import Mathlib\n#check Real.pi\n')
        run('full-Mathlib-import', [str(compiler), '--root='+str(out), '-j1',
            '-o', str(out/'GenericImport.olean'), str(probe)], out)
        owned = sum(p.stat().st_size for p in out.rglob('*')
                    if p.is_file() and not p.is_symlink())
        need(owned <= 300 << 30, 'owned generic setup scratch cap')
        need(sha(__file__) == controller_sha256, 'controller source unchanged during setup')
        save(out/'RESULT.json', {'status': 'PASS_CLEAN_PINNED_GENERIC_SETUP_AND_FULL_MATHLIB_IMPORT',
            'schema': 'RH_GENERIC_SETUP_V1', 'controller_sha256': controller_sha256,
            'PLAN_sha256': sha(out/'PLAN.json'), 'STAGES_sha256': sha(out/'STAGES.json'),
            'GENERIC_CONTEXT_sha256': sha(out/'GENERIC_CONTEXT.json'),
            'compiler_sha256': sha(compiler), 'packages': dependencies,
            'seconds': time.monotonic()-started,
            'peak_individual_child_RSS_KiB': max(p.get('peak_child_RSS_KiB', 0) for p in stages),
            'owned_regular_bytes_before_result': owned, 'application_objects_used': False,
            'network_downloads': 'Exact public pinned generic Git sources and official Mathlib build caches',
            'trust': 'Pinned generic compiler, core runtime and generic library cache infrastructure; '
                     'this is dependency setup, not source-first PV or an application theorem.'})
    except BaseException as error:
        save(out/'FAILURE.json', {'status': 'FAILED_GENERIC_SETUP_NOT_APPLICATION_PROOF',
             'error': repr(error), 'completed_stages': len(stages),
             'seconds': time.monotonic()-started})
        raise


if __name__ == '__main__':
    main()
