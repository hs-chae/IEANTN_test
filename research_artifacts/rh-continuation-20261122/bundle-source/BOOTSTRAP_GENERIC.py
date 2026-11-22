#!/usr/bin/env python3
"""Assemble fresh exact generic libraries, then run the unchanged legacy gate.

Requires clean manifest-pinned generic source checkouts and exact Lean compiler.
Downloads only from the official pinned archive list, builds cache-missing tools
from included pinned source inputs, and restores an owned metadata view. Never
uses or changes any existing generic/application proof object bank.
"""
from pathlib import Path
import argparse, copy, json, os, subprocess, sys, time
sys.dont_write_bytecode = True
from prepare_bundle import need, strict, sha, save, verify

def main():
    here = Path(__file__).resolve().parent
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--packages', type=Path, required=True)
    p.add_argument('--compiler', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    a = p.parse_args(); out = a.out.resolve(); compiler = a.compiler.resolve()
    need(not out.exists() and not out.is_relative_to(here), 'fresh bootstrap scratch outside bundle required')
    verify(here)
    source = here / 'network/Solutions/RHContinuation.v1'
    ctx = strict(source / 'scripts/GENERIC_CONTEXT.json')
    need(sha(compiler) == ctx['compiler_sha256'], 'exact compiler SHA256')
    leantar = compiler.parent / 'leantar'
    archive_manifest = strict(here / 'GENERIC_CACHE_ARCHIVES.json')
    need(leantar.is_file() and sha(leantar) == archive_manifest['leantar_sha256'], 'exact compiler-bundled leantar identity')
    packages = a.packages.resolve(); package_roots = {}
    for dep in ctx['generic_dependencies']:
        root = packages / dep['name']; need(root.is_dir(), 'missing pinned generic source checkout: ' + dep['name'])
        rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=root, text=True)
        need(rev == dep['revision'] and not dirty.strip(), 'wrong/dirty pinned generic source checkout: ' + dep['name'])
        package_roots[dep['name']] = root
        dep['path'] = str(root)
    recipe = here / 'generic-source-recipe'; r = strict(recipe / 'RECIPE.json')
    for row in r['modules']:
        rel = Path(row['source']).relative_to(Path('source') / row['library'])
        original = package_roots[row['library']] / rel
        need(original.is_file() and sha(original) == sha(recipe / row['source']), 'included generic source differs from pinned checkout: ' + row['module'])
    if a.check:
        out.mkdir(parents=True); save(out / 'RESULT.json', {'status': 'PASS_CLEAN_GENERIC_BOOTSTRAP_INPUTS_ONLY',
            'python_optimization': sys.flags.optimize, 'network_or_build_performed': False,
            'generic_source_modules': len(r['modules'])})
        print('PASS_CLEAN_GENERIC_BOOTSTRAP_INPUTS_ONLY'); return
    out.mkdir(parents=True); (out / 'logs').mkdir(); start = time.monotonic()
    env = os.environ.copy(); env['PATH'] = str(compiler.parent) + os.pathsep + env.get('PATH', '')
    env['PYTHONDONTWRITEBYTECODE'] = '1'; env.pop('LEAN_PATH', None)
    result = {'schema': 'CLEAN_GENERIC_BOOTSTRAP_TO_UNCHANGED_LEGACY_IDENTITY_V1', 'status': 'RUNNING',
              'validator_sha256': sha(__file__), 'compiler_sha256': sha(compiler),
              'leantar_sha256': sha(leantar), 'old_generic_semantic_objects_used': False,
              'application_objects_used': False, 'steps': []}
    save(out / 'RESULT.json', result)
    def child(label, cmd):
        command = [sys.executable, str(here / 'run_bounded.py'), '--record', str(out / (label + '-resources')),
                   '--limit-gib', '48', '--wall-seconds', '1800', '--', *cmd]
        run = subprocess.run(command, env=env, text=True, capture_output=True)
        (out / 'logs' / (label + '.stdout')).write_text(run.stdout)
        (out / 'logs' / (label + '.stderr')).write_text(run.stderr)
        result['steps'].append({'step': label, 'command': cmd, 'returncode': run.returncode})
        save(out / 'RESULT.json', result)
        need(run.returncode == 0, 'generic bootstrap step failed: ' + label)
        print('PASS', label, flush=True)
    try:
        downloaded = out / 'downloaded'
        child('download', [sys.executable, str(here / 'fetch_generic_cache.py'), '--manifest', str(here / 'GENERIC_CACHE_ARCHIVES.json'), '--out', str(downloaded)])
        bank = out / 'fresh-bank'; bank.mkdir()
        archives = sorted(downloaded.glob('*.ltar'))
        need(len(archives) == 8865, 'complete official archive count')
        config = out / 'unpack-config.json'
        save(config, [{'file': str(path), 'base': str(bank)} for path in archives])
        unpack = out / 'unpack.py'
        unpack.write_text('import json,subprocess\nfrom pathlib import Path\n'
            + 'command=' + repr([str(leantar), '-x', '-j', '-']) + '\n'
            + 'data=Path(' + repr(str(config)) + ').read_text()\n'
            + 'raise SystemExit(subprocess.run(command,input=data,text=True,cwd=' + repr(str(bank)) + ').returncode)\n')
        child('unpack', [sys.executable, str(unpack)])
        child('missing-source', [sys.executable, str(here / 'bootstrap_missing_generic.py'), '--recipe', str(recipe),
              '--fresh-bank', str(bank), '--compiler', str(compiler), '--out', str(out / 'missing-source')])
        ctx['compiler'] = str(compiler); replacements = {}
        for dep in ctx['generic_dependencies']:
            old = dep['library']; new = bank / ('.lake/build/lib/lean' if dep['name'] == 'mathlib'
                else '.lake/packages/' + dep['name'] + '/.lake/build/lib/lean')
            replacements[old] = str(new); dep['library'] = str(new); dep['library_present'] = new.is_dir()
        ctx['generic_libraries'] = [replacements[path] for path in ctx['generic_libraries']]
        ctx.update(new_application_object_root=None, source_root=None,
                   generic_cache_origin='Fresh official archive download plus38 pinned-source generic builds; no old generic/app semantic objects')
        context = out / 'fresh-context.json'; save(context, ctx)
        child('owned-view', [sys.executable, str(here / 'generic_transport.py'), 'restore', '--bundle', str(here),
            '--context', str(context), '--transport', str(here / 'generic-transport'), '--out', str(out / 'owned-view')])
        final_context = out / 'owned-view/GENERIC_CONTEXT.json'; final = strict(final_context)
        old = here / 'network/Solutions/RHExposureStudy.v1/Ramanujan640/REPRODUCE.py'
        cmd = [sys.executable, str(old), '--check', '--compiler', str(compiler)]
        for lib in strict(old.parent / 'SOURCE_MANIFEST.json')['generic_libraries']:
            matches = [d for d in final['generic_dependencies'] if d['name'] == lib['name']]
            need(len(matches) == 1, 'legacy generic source/library association')
            cmd += ['--generic-root', lib['name'] + '=' + matches[0]['library']]
        child('unchanged-old146-input-gate', cmd)
        need(sha(__file__) == result['validator_sha256'], 'bootstrap entry changed during run')
        result.update(status='PASS_FRESH_GENERIC_BOOTSTRAP_AND_UNCHANGED_LEGACY_FULL_INVENTORY_GATE',
                      elapsed_seconds=time.monotonic() - start, generic_context=str(final_context),
                      generic_context_sha256=sha(final_context), application_proofs_rebuilt_in_this_command=False,
                      archival_metadata_policy='Exact .trace/.hash/zero-byte marker plus one explicitly approved IDE reference .ilean restored byte-for-byte; every other generic file matches the original full inventory before old validator accepts.')
        save(out / 'RESULT.json', result); print(result['status'], str(final_context))
    except BaseException as error:
        result.update(status='FAILED_OR_PARTIAL_CLEAN_GENERIC_BOOTSTRAP', error=str(error), elapsed_seconds=time.monotonic() - start)
        save(out / 'RESULT.json', result); raise

if __name__ == '__main__':
    main()
