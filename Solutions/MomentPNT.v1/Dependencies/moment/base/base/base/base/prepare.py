"""Freeze an additive source-only actual-frame/weight/PNT replay component.

Maintainer assembly only. It never reads application objects. Clean reproduction
uses reproduce_all.py, which first runs the unchanged distributed base recipe.
"""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import re
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
    need(not target.exists() or sha(target) == sha(path), 'immutable assembly ' + str(relative))
    target.write_bytes(path.read_bytes())
    return str(relative)

def normalized(text):
    text = text.replace('by native_decide', 'by decide +kernel')
    text = text.replace('(the Ramanujan–Soldner constant, `1.0451…`).', '(the fixed value `1.0451…`).')
    ignored = {'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000'}
    return '\n'.join(s for s in text.splitlines() if s.strip() and s.strip() not in ignored)

def main():
    need(not (B / 'SOURCE_LOCK.json').exists(), 'immutable lock already exists')
    archive = R / 'research/SOURCE_PNT_COMPOSITION_SOURCE_ONLY_COMPONENT_V1.zip'
    need(sha(archive) == '0212e0c1bdc774e458cc3d19a4b2f5aaa0a22cb01c39fb375f13cffce45a92d0',
         'original base archive identity')
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read('CAPSULE_MANIFEST.json'))
        need(manifest['application_objects_included'] == [], 'source-only base')
        listed = {row['path']: row for row in manifest['files']}
        need(set(z.namelist()) == set(listed) | {'CAPSULE_MANIFEST.json'}, 'complete base archive population')
        for member in z.infolist():
            rel = Path(member.filename)
            need(not rel.is_absolute() and '..' not in rel.parts and not member.is_dir(), 'regular relative archive path')
            need((member.external_attr >> 16) & 0o170000 != 0o120000, 'no archive symlink')
            data = z.read(member)
            if member.filename in listed:
                row = listed[member.filename]
                need(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
                     'base archive member ' + member.filename)
            target = B / 'base' / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            need(not target.exists() or target.read_bytes() == data, 'unchanged base member')
            target.write_bytes(data)
    base = json.loads((B / 'base/SOURCE_LOCK.json').read_text())
    need(len(base['sources']) == 1412 and len(base['roots']) == 2350, 'fixed base population')
    main_dir = R / 'research/source-height-main-capsule-v1'
    main_lock = json.loads((main_dir / 'SOURCE_LOCK.json').read_text())
    need(len(main_lock['sources']) == 416, 'fixed original main snapshot')
    for k in ['compiler_sha256', 'runtime_pins', 'generic_dependencies']:
        need(base[k] == main_lock[k], 'same compiler/public dependencies ' + k)
    base_rows = {x['module']: x for x in base['sources']}
    main_rows = {x['module']: x for x in main_lock['sources']}
    variants = []
    for name in sorted(base_rows.keys() & main_rows.keys()):
        a, b = base_rows[name], main_rows[name]
        if a['sha256'] == b['sha256']:
            continue
        old, selected = main_dir / b['path'], B / 'base' / a['path']
        need(sha(old) == b['sha256'] and normalized(old.read_text()) == normalized(selected.read_text()),
             'only previously recorded proof/comment variant ' + name)
        rel = Path('provenance/original-main-variants') / Path(name.replace('.', '/')).with_suffix('.lean')
        copy(old, rel)
        diff = ''.join(difflib.unified_diff(old.read_text().splitlines(True), selected.read_text().splitlines(True),
                    fromfile='original-main/' + name, tofile='unchanged-selected-base/' + name))
        dp = B / 'provenance/diffs' / Path(name.replace('.', '/')).with_suffix('.diff')
        dp.parent.mkdir(parents=True, exist_ok=True)
        dp.write_text(diff)
        variants.append(dict(module=name, original_source=str(rel), original_sha256=sha(old),
                             selected_base_sha256=sha(selected), diff=str(dp.relative_to(B))))
    need([x['module'] for x in variants] == ['EulerGammaBound', 'HeightProfileScalars',
         'IEANTN.Vocabulary.PrimeCounting', 'OriginalBoundaryScalars', 'OriginalScalars', 'ReversAmplitude'],
         'exact six inherited proof/comment variants')
    scanner_path = R / 'scoped/body43-supplement-v1/prepare_snapshot.py'
    spec = importlib.util.spec_from_file_location('existing_import_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    copy(scanner_path, 'provenance/import_scanner.py')
    env = json.loads((R / 'research/source-pnt-composition-preflight-resume-v1/OO-environment.json').read_text())
    generic = [Path(d['objects']) for d in env['generic_dependencies']]
    generic.append(Path(env['compiler']).parent.parent / 'lib/lean')
    roots = [n for n in main_lock['roots'] if n not in base['roots']]
    source = {}
    origins = {}
    search = [R / p for p in ['research/analytic/lean', 'research/framed-points-v1/source',
        'research/framed-point-aggregate-v1/source', 'research/main-weight-v1/frozen-v1/source',
        'research/main-weight-v1/aggregate-source-v5', 'research/basis-source/lean',
        'scoped/frontend/lean', 'scoped/stdio-v1/lean']]
    def locate(name):
        if name in main_rows:
            row = main_rows[name]
            p = main_dir / row['path']
            need(sha(p) == row['sha256'], 'original main pin ' + name)
            return p
        rel = Path(name.replace('.', '/')).with_suffix('.lean')
        candidates = [root / rel for root in search if (root / rel).is_file()]
        need(candidates and len({sha(p) for p in candidates}) == 1, 'unique source-only dependency ' + name)
        return candidates[0]
    queue = list(main_lock['root_modules']) + ['SourceMainWeightsV1.PNT', 'SourceMainWeightsV1.PrimeRich']
    cursor = 0
    while cursor < len(queue):
        name = queue[cursor]
        cursor += 1
        if name in base_rows or name in source:
            continue
        rel = Path(name.replace('.', '/')).with_suffix('.olean')
        if any((root / rel).is_file() for root in generic):
            continue
        p = locate(name)
        source[name] = p
        origins[name] = str(p.relative_to(R))
        queue.extend(scanner.imports(p.read_text()))
    all_names = set(source) | set(base_rows)
    state, ordered = {}, []
    def visit(name):
        if name in state:
            need(state[name] == 'done', 'acyclic append source graph ' + name)
            return
        state[name] = 'active'
        p = source[name]
        imports = [n for n in scanner.imports(p.read_text()) if n in all_names]
        for child in imports:
            if child in source:
                visit(child)
        need('include_str' not in p.read_text(), 'new explicit payload discovery required ' + name)
        rel = Path('source') / Path(name.replace('.', '/')).with_suffix('.lean')
        copy(p, rel)
        ordered.append(dict(module=name, path=str(rel), sha256=sha(p), bytes=p.stat().st_size,
                            imports=imports, original_source=origins[name]))
        state[name] = 'done'
    for name in sorted(source):
        visit(name)
    for name, p in sorted(source.items()):
        text = p.read_text()
        namespaces = re.findall(r'^namespace\s+([\w.]+)', text, re.M)
        prefix = namespaces[0] if namespaces else ''
        for token in re.findall(r'^#print axioms\s+([\w.]+)', text, re.M):
            full = token if token.startswith(('Scoped', 'Synergy', 'Source')) else prefix + '.' + token
            roots.append(full)
        roots.extend(re.findall(r'(?<!`)`(?!`)((?:SourceMainFramesV1|SourceMainWeightsV1)\.[\w.]+)', text))
    roots = list(dict.fromkeys(roots))
    need(set(source) >= {f'SourceMainFramesV1.Point{i:04d}' for i in range(768)}, 'all actual framed point proofs')
    need(set(source) >= {f'SourceMainWeightsV1.Block{i:02d}' for i in range(24)}, 'all actual kernel weight chunks')
    need('SourceMainWeightsV1.PNT.source_pi_actual_weights' in roots, 'actual final consumer selected')
    need(len(source) == len(ordered) and len(set(roots)) == len(roots), 'unique source and compiler identities')
    receipts = ['research/analytic/MAIN_WEIGHT_DOMAIN_ABSTRACTION_FIX_V1.json',
                'research/main-weight-v1/frozen-v1/PLAN.json', 'research/framed-points-v1/PLAN.json',
                'research/main-weight-v1/aggregate-v5/RECEIPT.json',
                'research/main-weight-v1/PNT-generic-v2/RECEIPT.json',
                'research/main-weight-v1/final-PNT-v1/RECEIPT.json',
                'research/main-weight-v1/prime-rich-v1/RECEIPT.json',
                'research/main-weight-v1/source-caps-accepted-v5/RECEIPT.json']
    for raw in receipts:
        copy(R / raw, Path('evidence/original-host') / raw.removeprefix('research/'))
    lock = dict(schema='ACTUAL_MAIN_FRAME_WEIGHT_PNT_SOURCE_APPEND_V1',
        compiler_sha256=base['compiler_sha256'], runtime_pins=base['runtime_pins'],
        generic_dependencies=base['generic_dependencies'], base_source_lock_sha256=sha(B / 'base/SOURCE_LOCK.json'),
        base_source_modules=1412, base_theorem_roots=2350, sources=ordered, payloads=[],
        roots=roots, root_modules=[x['module'] for x in ordered],
        full_program_source_first_PV=False, combined_fresh_replay_completed=False,
        qualification='Source-only append to the unchanged bare1412 replay. Actual framed point executions, exact C-expression kernel weight sum and conditional ANT theorem; full main/startup/weight-loop/I/O/run association remains separate.')
    (B / 'SOURCE_LOCK.json').write_text(json.dumps(lock, indent=2) + '\n')
    provenance = dict(status='SOURCE_ONLY_PREPARED_NOT_REPLAYED', base_archive_sha256=sha(archive),
        base_archive_members=2086, selected_base_source_modules=1412, delta_source_modules=len(ordered),
        delta_theorem_roots=len(roots), inherited_main_proof_comment_variants=variants,
        application_objects_read_or_copied=[], source_lock_sha256=sha(B / 'SOURCE_LOCK.json'))
    (B / 'PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps({k: provenance[k] for k in ['status', 'delta_source_modules', 'delta_theorem_roots', 'source_lock_sha256']}))

if __name__ == '__main__':
    main()
