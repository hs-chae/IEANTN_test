#!/usr/bin/env python3
"""Inventory the actual generic source import DAG of the frozen693 proof scope.

Preserves all existing generic caches and application sources/objects. A source
header inventory is separate from the subsequent real Lean import/build probe.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[4]
SCOPE = ROOT/'Solutions/RHOcticPush.v1'
ALIASES = {'Mathlib': 'mathlib', 'Batteries': 'batteries', 'Aesop': 'aesop',
    'Qq': 'Qq', 'ProofWidgets': 'proofwidgets', 'ImportGraph': 'importGraph',
    'LeanSearchClient': 'LeanSearchClient', 'Plausible': 'plausible', 'Cli': 'Cli'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--context', required=True, type=Path)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--append-source-manifest', action='append', type=Path, default=[])
    p.add_argument('--expected-application-modules', type=int, default=693)
    a = p.parse_args()
    need(not a.out.exists(), 'fresh generic preflight inventory')
    ctx = read(a.context)
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'pinned compiler')
    for dep in ctx['generic_dependencies']:
        cp = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=dep['path'], capture_output=True, text=True)
        need(cp.returncode == 0 and cp.stdout.strip() == dep['revision'], 'generic source revision')
        need(subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=dep['path']).returncode == 0,
             'generic tracked source drift')
    primary = SCOPE/'integration/corrected/capture/SOURCE_CLOSURE.json'
    manifests = [ROOT/x['path'] for x in read(primary)['baseline_manifests']]
    manifests += [primary, SCOPE/'integration/supplement/audit-corrected-capture/SOURCE_CLOSURE.json',
        SCOPE/'box/zero/cold-capture/SOURCE_CLOSURE.json',
        SCOPE/'integration/closed_box/capture/SOURCE_CLOSURE.json']
    manifests += [q.resolve() for q in a.append_source_manifest]
    roots, selected, application_rows = set(), [], []
    for path in manifests:
        for row in read(path)['modules']:
            roots.update(row.get('generic_imports', []))
            selected.append(row['module'])
            application_rows.append(row)
    need(len(selected) == len(set(selected)) == a.expected_application_modules,
         'exact explicitly selected application scope')
    parser = ROOT/'Solutions/RHLimit.v1/scripts/prepare_pi_manifest.py'
    code = parser.read_text()
    old = "if line=='prelude':"
    need(code.count(old) == 1, 'exact existing source-header parser variant')
    namespace = dict(__file__=str(parser), __name__='generic_source_header_only')
    exec(compile(code.replace(old, "if line in ['prelude','module']:"), str(parser), 'exec'), namespace)
    header = namespace['header_imports']
    actual_generic = set()
    for row in application_rows:
        source = Path(row['path'])
        source = source if source.is_absolute() else ROOT/source
        need(sha(source) == row['sha256'], 'actual selected application source pin')
        for mod in header(source.read_text()):
            if mod == 'all' or mod in selected:
                continue
            need(mod.split('.')[0] in {*ALIASES, 'Lean', 'Init', 'Std', 'Lake'},
                 'unmapped actual application import: '+mod)
            actual_generic.add(mod)
    root_difference = dict(source_only=sorted(actual_generic-roots), metadata_only=sorted(roots-actual_generic))
    declared_roots = sorted(roots)
    # Some historical capture schemas omit generic_imports. Actual pinned
    # source headers, rather than metadata sparsity, define this inventory.
    roots = actual_generic
    deps = {q['name']: q for q in ctx['generic_dependencies']}
    seen, active, ordered = {}, set(), []
    def visit(mod):
        prefix = mod.split('.')[0]
        if mod in seen or prefix in ['Lean', 'Init', 'Std', 'Lake']:
            return
        need(mod not in active and prefix in ALIASES, 'unmapped or cyclic generic module: '+mod)
        active.add(mod)
        dep = deps[ALIASES[prefix]]
        source = Path(dep['path'])/Path(*mod.split('.')).with_suffix('.lean')
        need(source.is_file(), 'pinned generic source missing: '+mod)
        # Lean's `import all X` requests private declarations of X; `all` is
        # syntax, not a module. The later actual import probe checks sidecars.
        imports = [name for name in header(source.read_text()) if name != 'all']
        for child in imports:
            visit(child)
        obj = Path(dep['library'])/Path(*mod.split('.')).with_suffix('.olean')
        row = dict(module=mod, source=str(source), source_sha256=sha(source),
                   object=str(obj), object_exists=obj.is_file(), imports=imports)
        seen[mod] = row
        ordered.append(row)
        active.remove(mod)
    for mod in sorted(roots):
        visit(mod)
    result = dict(status='SELECTED_GENERIC_SOURCE_CLOSURE_INVENTORIED_NOT_YET_IMPORT_TESTED',
        selected_application_modules=a.expected_application_modules,
        actual_application_source_headers_checked=True, generic_roots=sorted(roots), modules=ordered,
        declared_generic_roots=declared_roots, source_metadata_difference=root_difference,
        missing_objects=[q for q in ordered if not q['object_exists']], context=ctx,
        original_context_sha256=sha(a.context), controller_sha256=sha(__file__),
        manifests=[dict(path=str(q), sha256=sha(q)) for q in manifests],
        header_parser_note='Existing comment-aware parser with explicit Lean4 module-header admission; actual Lean import/build probe is a separate gate.')
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(generic_modules=len(ordered), missing=len(result['missing_objects']),
        missing_names=[q['module'] for q in result['missing_objects']])))

if __name__ == '__main__':
    main()
