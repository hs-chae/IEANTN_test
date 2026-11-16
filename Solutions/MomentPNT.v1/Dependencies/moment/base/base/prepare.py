"""Freeze the rational/source-profile overlay without changing prior inputs.

Assembly reads only source/evidence and the accepted-source inventory. It never
borrows application objects and never counts a prepared graph as a passed run.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import shutil
import zipfile

B = Path(__file__).resolve().parent
R = B.parents[1]

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def copy(path, relative):
    target = B / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    need(not target.exists() or sha(target) == sha(path), 'immutable source snapshot: ' + str(relative))
    shutil.copy2(path, target)

def main():
    need(not (B / 'SOURCE_LOCK.json').exists(), 'immutable snapshot already exists')
    archive = R / 'research/SOURCE_COMPLETE_MAIN_OBSERVED_ANT_SOURCE_ONLY_COMPONENT_V1.zip'
    need(sha(archive) == 'b930c86798ef91623ea24062b2308d84c7958d7d33cc67380d0c7be24ba0ccd1', 'prior3942 source input identity')
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read('CAPSULE_MANIFEST.json'))
        need(manifest['application_objects_included'] == [], 'source/evidence only')
        rows = {r['path']: r for r in manifest['files']}
        need(set(z.namelist()) == set(rows) | {'CAPSULE_MANIFEST.json'}, 'complete archive population')
        for item in z.infolist():
            rel = Path(item.filename)
            need(not rel.is_absolute() and '..' not in rel.parts and not item.is_dir(), 'regular relative archive member')
            need((item.external_attr >> 16) & 0o170000 != 0o120000, 'no archive symlink')
            data = z.read(item)
            if item.filename in rows:
                row = rows[item.filename]
                need(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'], 'prior member identity')
            p = B / 'base' / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
    levels = [('base', 'source'), ('base/base', 'source'), ('base/base/base', 'source')]
    previous = []
    locks = []
    for prefix, root in levels:
        path = B / prefix / 'SOURCE_LOCK.json'
        lock = json.loads(path.read_text())
        locks.append(lock)
        for row in lock['sources']:
            previous.append(dict(row, path=str(Path(prefix) / row['path']),
                                 source_root=str(Path(prefix) / root)))
    need(len(previous) == len({r['module'] for r in previous}) == 3942, 'exact prior3942 identities')
    old_names = {r['module'] for r in previous}
    index_path = R / 'research/analytic/RESUME_ACTUAL_SOURCE_PROGRESS_V12.json'
    index = json.loads(index_path.read_text())
    accepted = {r['module']: r for r in index['components']}
    slope_path = R / 'research/point-slope-v1/PLAN.json'
    slope = json.loads(slope_path.read_text())
    slopes = {r['module']: r for r in slope['source_blocks']}
    scanner_path = R / 'scoped/body43-supplement-v1/prepare_snapshot.py'
    spec = importlib.util.spec_from_file_location('source_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    copy(scanner_path, 'provenance/import_scanner.py')
    env = json.loads((R / 'research/source-pnt-composition-preflight-resume-v1/OO-environment.json').read_text())
    generic = [Path(d['objects']) for d in env['generic_dependencies']]
    generic.append(Path(env['compiler']).parent.parent / 'lib/lean')
    search = [R / p for p in ['research/analytic/lean', 'research/basis-source/lean',
        'research/point-slope-v1/source', 'scoped/frontend/lean', 'scoped/stdio-v1/lean']]
    queue = ['SynergyHeightC.MainRationalProgram', 'SynergyHeightC.MainPrimeRichRefined',
             'SynergyHeightC.MainModelOnlyClosedAudit']
    source = {}
    cursor = 0
    while cursor < len(queue):
        name = queue[cursor]
        cursor += 1
        if name in old_names or name in source:
            continue
        rel = Path(name.replace('.', '/'))
        if any((root / rel.with_suffix('.olean')).is_file() for root in generic):
            continue
        candidates = [root / rel.with_suffix('.lean') for root in search
                      if (root / rel.with_suffix('.lean')).is_file()]
        need(candidates and len({sha(p) for p in candidates}) == 1, 'unique new source identity: ' + name)
        path = candidates[0]
        if name in accepted:
            need(sha(path) == accepted[name]['source_sha256'], 'frozen V12 accepted source: ' + name)
        if name in slopes:
            need(sha(path) == slopes[name]['sha256'], 'frozen accepted slope block: ' + name)
        source[name] = path
        queue.extend(scanner.imports(path.read_text()))
    need({f'SourcePointSlopesV1.Block{i:02d}' for i in range(96)} <= set(source), 'all96 actual slope blocks')
    all_names = old_names | set(source)
    state, ordered = {}, []
    def visit(name):
        if name in state:
            need(state[name] == 'done', 'acyclic new proof graph: ' + name)
            return
        state[name] = 'active'
        path = source[name]
        imports = [n for n in scanner.imports(path.read_text()) if n in all_names]
        for n in imports:
            if n in source:
                visit(n)
        need('include_str' not in path.read_text() and 'include_bytes' not in path.read_text(), 'new payload inventory required')
        relative = Path('source') / Path(name.replace('.', '/')).with_suffix('.lean')
        copy(path, relative)
        ordered.append(dict(module=name, path=str(relative), source_root='source', sha256=sha(path),
                            bytes=path.stat().st_size, imports=imports,
                            original_source=str(path.relative_to(R))))
        state[name] = 'done'
    for name in sorted(source):
        visit(name)
    roots = []
    for name, path in sorted(source.items()):
        text = path.read_text()
        namespaces = re.findall(r'^namespace\s+([\w.]+)', text, re.M)
        prefix = namespaces[0] if namespaces else ''
        for token in re.findall(r'^#print axioms\s+([\w.]+)', text, re.M):
            roots.append(token if token.startswith(('Scoped', 'Source', 'Synergy')) else prefix + '.' + token)
        roots.extend(re.findall(r'(?<!`)`(?!`)((?:SourcePointSlopesV1)\.[\w.]+)', text))
    roots = list(dict.fromkeys(roots))
    combined_roots = list(dict.fromkeys([r for frozen in reversed(locks) for r in frozen['roots']] + roots))
    combined_modules = [r['module'] for r in previous] + [r['module'] for r in ordered]
    for raw, relative in [
        ('research/analytic/RESUME_ACTUAL_SOURCE_PROGRESS_V12.json', 'evidence/FROZEN_SOURCE_INDEX_V12.json'),
        ('research/point-slope-v1/PLAN.json', 'evidence/ACCEPTED_SLOPE_PLAN.json'),
        ('research/point-slope-v1/all-v1/RECEIPT.json', 'evidence/SLOPE_ALL_RECEIPT.json'),
        ('research/analytic/RATIONAL_REFINEMENT_REVIEW_CONTROLS_V1.json', 'evidence/INDEPENDENT_REVIEW.json')]:
        copy(R / raw, relative)
    lock = dict(schema='FROZEN_RATIONAL_PROFILE_SOURCE_OVERLAY_V1',
        compiler_sha256=locks[0]['compiler_sha256'], runtime_pins=locks[0]['runtime_pins'],
        generic_dependencies=locks[0]['generic_dependencies'], prior_source_modules=3942,
        prior_source_lock_sha256=sha(B / 'base/SOURCE_LOCK.json'), sources=ordered, payloads=[],
        roots=roots, root_modules=[r['module'] for r in ordered],
        combined_sources=previous + ordered, combined_roots=combined_roots,
        combined_root_modules=list(dict.fromkeys([r for frozen in reversed(locks) for r in frozen['root_modules']]
                                                + [r['module'] for r in ordered])),
        final_source_root='SynergyHeightC.MainRationalProgram.main_observed_rational_profile',
        kernel_only_root='SynergyHeightC.MainRationalClosed.kernel_only_profile_point',
        mathematical_inputs_unchanged=True, C_programs_unchanged=True,
        completed_fresh_source_graph=False, namespace_isolated=False,
        qualification='Prepared stronger rational-profile/source-main and closed kernel-only comparison overlay. Selected11976-root3942 source input remains immutable. Complete combined source-cold and namespace replay remains pending.')
    (B / 'SOURCE_LOCK.json').write_text(json.dumps(lock, indent=2) + '\n')
    provenance = dict(status='PREPARED_SOURCE_ONLY_RATIONAL_OVERLAY_NOT_REPLAYED',
        prior_archive_sha256=sha(archive), prior_modules=3942, additional_modules=len(ordered),
        combined_modules=len(combined_modules), additional_distinct_roots=len(roots),
        combined_distinct_roots=len(combined_roots), source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
        accepted_index_sha256=sha(index_path), accepted_slope_plan_sha256=sha(slope_path),
        application_objects_read_or_copied=[], strengthened_kernel_only_comparator_matches_math=True,
        fresh_independent_kernel_only_build_claimed=False, causal_PV_necessity_claimed=False)
    (B / 'PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps(provenance))

if __name__ == '__main__':
    main()
