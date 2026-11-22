#!/usr/bin/env python3
"""Compile cache-missing generic tooling from exact pinned source/build inputs.

All generic import artifact paths are redirected to the fresh official bank.
Compiler/core libraries come from the exact compiler installation. No application
objects or original host generic semantic objects are in the import boundary.
"""
from pathlib import Path
import argparse, json, os, shutil, subprocess, sys, time
sys.dont_write_bytecode = True
from prepare_bundle import need, safe, strict, sha, save

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--recipe', type=Path, required=True)
    p.add_argument('--fresh-bank', type=Path, required=True)
    p.add_argument('--compiler', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(); recipe = a.recipe.resolve(); bank = a.fresh_bank.resolve(); out = a.out.resolve()
    need(not out.exists(), 'fresh build record required')
    r = strict(recipe / 'RECIPE.json'); compiler = a.compiler.resolve()
    need(sha(compiler) == r['compiler_sha256'], 'compiler identity')
    for entry in r['files']:
        path = recipe / safe(entry['path'])
        need(path.is_file() and path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'], 'recipe input identity')
    modules = {row['module']: row for row in r['modules']}
    need(len(modules) == len(r['modules']) == 38 and r['legacy_missing_modules'] == 37,
         'exact37legacytoolsplusoneCliBasicprerequisiteinventory')
    roots = {name: bank / ('.lake/build/lib/lean' if name == 'mathlib'
                         else '.lake/packages/' + name + '/.lake/build/lib/lean')
             for name in r['original_generic_roots']}
    for root in roots.values():
        root.mkdir(parents=True, exist_ok=True)
    replacements = {old: str(roots[name]) for name, old in r['original_generic_roots'].items()}
    core = compiler.parent.parent / 'lib/lean'
    replacements[r['original_compiler_library']] = str(core)
    def relocate(value):
        if isinstance(value, str):
            for old, new in sorted(replacements.items(), key=lambda item: -len(item[0])):
                if value == old or value.startswith(old + '/'):
                    return new + value[len(old):]
            return value
        if isinstance(value, list):
            return [relocate(x) for x in value]
        if isinstance(value, dict):
            return {key: relocate(v) for key, v in value.items()}
        return value
    visiting = set(); built = set(); order = []
    def visit(name):
        if name in built:
            return
        need(name not in visiting, 'generic source dependency cycle')
        visiting.add(name); setup = strict(recipe / modules[name]['setup'])
        for dep in setup.get('importArts', {}):
            if dep in modules:
                visit(dep)
        visiting.remove(name); built.add(name); order.append(name)
    for name in modules:
        visit(name)
    out.mkdir(parents=True); (out / 'logs').mkdir(); (out / 'setup').mkdir()
    shutil.copyfile(Path(__file__).resolve(), out / 'bootstrap_missing_generic.executed.py')
    env = os.environ.copy(); env['LEAN_PATH'] = ':'.join(str(root) for root in roots.values())
    env['PATH'] = str(compiler.parent) + os.pathsep + env.get('PATH', '')
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = {'schema': 'FRESH_OFFICIAL_GENERIC_BANK_SOURCE_SUPPLEMENT_V1', 'status': 'RUNNING',
              'recipe_sha256': sha(recipe / 'RECIPE.json'), 'compiler_sha256': sha(compiler),
              'controller_sha256': sha(__file__),
              'original_generic_semantic_objects_used': False, 'application_objects_used': False, 'modules': []}
    save(out / 'RESULT.json', result); started = time.monotonic()
    for name in order:
        row = modules[name]; setup = relocate(strict(recipe / row['setup']))
        # Cached setup files can retain CI paths from several source roots.
        # Resolve each explicit module artifact by its inventory owner, never
        # by accepting any of those historical absolute directory spellings.
        for dep, arrays in setup.get('importArts', {}).items():
            owner = r['generic_module_owners'].get(dep)
            root = roots[owner] if owner is not None else core
            rel = dep.replace('.', '/')
            for array in arrays:
                for index, raw in enumerate(array):
                    ending = raw.rsplit('/' + rel, 1)
                    need(len(ending) == 2 and ending[1] in {'.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'},
                         'unrecognized generic module artifact spelling: ' + raw)
                    array[index] = str(root / (rel + ending[1]))
                for raw in array:
                    target = Path(raw).resolve()
                    need(any(target.is_relative_to(root.resolve()) for root in [*roots.values(), core]),
                         'old or unadmitted generic import artifact path: ' + raw)
                    need(target.is_file(), 'missing fresh generic import artifact: ' + raw)
        setup_path = out / 'setup' / (name + '.json'); save(setup_path, setup)
        rel = Path(name.replace('.', '/')); obj = roots[row['library']] / rel.with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        source = recipe / row['source']; need(not obj.exists(), 'do not overwrite any downloaded generic object')
        cfile = out / (name + '.c')
        command = [str(compiler), '-j1', '-R', str(recipe / row['source_root']), str(source),
                   '-o', str(obj), '-i', str(obj.with_suffix('.ilean')), '-c', str(cfile),
                   '--setup', str(setup_path), '--json']
        t = time.monotonic(); run = subprocess.run(['/usr/bin/time', '-v', *command], cwd=recipe / row['source_root'], env=env, text=True, capture_output=True)
        (out / 'logs' / (name + '.stdout')).write_text(run.stdout)
        (out / 'logs' / (name + '.stderr')).write_text(run.stderr)
        result['modules'].append({'library': row['library'], 'module': name, 'command': command,
            'returncode': run.returncode, 'seconds': time.monotonic() - t, 'source_sha256': sha(source),
            'relocated_setup_sha256': sha(setup_path), 'object_sha256': sha(obj) if obj.is_file() else None})
        save(out / 'RESULT.json', result)
        need(run.returncode == 0, 'generic source bootstrap failed: ' + name)
        print(name, run.returncode, round(time.monotonic() - t, 3), flush=True)
    need(sha(__file__) == result['controller_sha256'], 'bootstrap controller changed during run')
    result.update(status='PASS38_PINNED_GENERIC_SOURCE_SUPPLEMENTS_NO_ORIGINAL_GENERIC_OBJECTS',
                  elapsed_seconds=time.monotonic() - started,
                  next_gate='Full unchanged legacy semantic file SHA256 comparison and owned metadata transport view before any application proof replay')
    save(out / 'RESULT.json', result); print(result['status'])

if __name__ == '__main__':
    main()
