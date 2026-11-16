"""Freeze a separate complete-main extension; never read application objects.

This maintainer assembly preserves the previously published input capsules and
their mathematical sources. It is not a completed source-cold replay receipt.
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
    need(not target.exists() or sha(target) == sha(path), 'immutable source assembly: ' + str(relative))
    shutil.copy2(path, target)
    return str(relative)

def main():
    need(not (B / 'SOURCE_LOCK.json').exists(), 'new immutable source snapshot required')
    archive = R / 'research/SOURCE_ACTUAL_FRAME_WEIGHT_PNT_SOURCE_ONLY_COMPONENT_V2.zip'
    need(sha(archive) == '76a0a59cbfa00637919ff62958dd67d8fe902df6c693ef8e7449e31be0ceb8ca',
         'corrected prior source-only capsule identity')
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read('CAPSULE_MANIFEST.json'))
        need(manifest['application_objects_included'] == [], 'prior source-only archive')
        rows = {row['path']: row for row in manifest['files']}
        need(set(z.namelist()) == set(rows) | {'CAPSULE_MANIFEST.json'}, 'complete prior source archive population')
        for item in z.infolist():
            rel = Path(item.filename)
            need(not rel.is_absolute() and '..' not in rel.parts and not item.is_dir(), 'regular relative member')
            need((item.external_attr >> 16) & 0o170000 != 0o120000, 'no member symlink')
            data = z.read(item)
            if item.filename in rows:
                row = rows[item.filename]
                need(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
                     'prior archive member identity: ' + item.filename)
            target = B / 'base' / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    append = json.loads((B / 'base/SOURCE_LOCK.json').read_text())
    original = json.loads((B / 'base/base/SOURCE_LOCK.json').read_text())
    prior = {row['module']: row for lock in [original, append] for row in lock['sources']}
    need(len(prior) == 2272, 'exact complete prior source compiler identities')
    scanner_path = R / 'scoped/body43-supplement-v1/prepare_snapshot.py'
    spec = importlib.util.spec_from_file_location('existing_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    copy(scanner_path, 'provenance/import_scanner.py')
    env = json.loads((R / 'research/source-pnt-composition-preflight-resume-v1/OO-environment.json').read_text())
    generic = [Path(d['objects']) for d in env['generic_dependencies']]
    generic.append(Path(env['compiler']).parent.parent / 'lib/lean')
    search = [R / p for p in ['research/analytic/lean', 'research/basis-source/lean',
        'research/source-budget-v1/source', 'research/source-budget-v1-assembly/source',
        'research/source-edges-v1/source', 'research/source-edges-v1/assembly-source',
        'research/framed-point-aggregate-v1/source', 'scoped/stdio-v1/lean', 'scoped/frontend/lean']]
    source = {}
    queue = ['SynergyHeightC.MainObservedProgram']
    cursor = 0
    while cursor < len(queue):
        name = queue[cursor]
        cursor += 1
        if name in prior or name in source:
            continue
        rel = Path(name.replace('.', '/'))
        if any((p / rel.with_suffix('.olean')).is_file() for p in generic):
            continue
        candidates = [p / rel.with_suffix('.lean') for p in search if (p / rel.with_suffix('.lean')).is_file()]
        need(candidates and len({sha(p) for p in candidates}) == 1, 'unique source dependency: ' + name)
        source[name] = candidates[0]
        queue.extend(scanner.imports(candidates[0].read_text()))
    state, ordered = {}, []
    all_names = set(source) | set(prior)
    def visit(name):
        if name in state:
            need(state[name] == 'done', 'acyclic complete-main graph: ' + name)
            return
        state[name] = 'active'
        path = source[name]
        imports = [n for n in scanner.imports(path.read_text()) if n in all_names]
        for child in imports:
            if child in source:
                visit(child)
        need('include_str' not in path.read_text() and 'include_bytes' not in path.read_text(),
             'explicit new payload discovery needed: ' + name)
        rel = Path('source') / Path(name.replace('.', '/')).with_suffix('.lean')
        copy(path, rel)
        ordered.append(dict(module=name, path=str(rel), sha256=sha(path), bytes=path.stat().st_size,
                            imports=imports, original_source=str(path.relative_to(R))))
        state[name] = 'done'
    for name in sorted(source):
        visit(name)
    roots = []
    for name, path in sorted(source.items()):
        text = path.read_text()
        namespaces = re.findall(r'^namespace\s+([\w.]+)', text, re.M)
        namespace = namespaces[0] if namespaces else ''
        for token in re.findall(r'^#print axioms\s+([\w.]+)', text, re.M):
            roots.append(token if token.startswith(('Scoped', 'Synergy', 'Source')) else namespace + '.' + token)
        roots.extend(re.findall(r'(?<!`)`(?!`)((?:SourceMainBudgetV1|SourceHeightEdgesV1|SourceMainFramesV1)\.[\w.]+)', text))
    roots = list(dict.fromkeys(roots))
    need('SynergyHeightC.MainObservedProgram.complete_source_main_observed_and_pnt' in roots, 'final observed ANT consumer')
    need({f'SourceMainBudgetV1.Cell{i:04d}' for i in range(768)} <= set(source), 'all actual budget cells')
    need(sum(n.startswith('SourceHeightEdgesV1.Edge') for n in source) == 768, 'all actual input-edge constructors')
    artifacts = [
        ('research/analytic/generate_main_observation.py', 'provenance/generate_main_observation_original.py'),
        ('research/height-main-cpp-fresh-v1/output.bin', 'evidence/observation/original-output.bin'),
        ('research/height-main-cpp-fresh-v1/RECEIPT.json', 'evidence/observation/ORIGINAL_CPP_RECEIPT.json'),
        ('research/height-main-observation-v1/observed-total.bin', 'evidence/observation/observed-total.bin'),
        ('research/height-main-observation-v1/PREPARATION.json', 'evidence/observation/ORIGINAL_PREPARATION.json'),
        ('research/analytic/MAIN_COMPLETE_MODEL_REVIEW_CONTROLS_V1.json', 'evidence/reviews/MODELED_PROGRAM.json'),
        ('research/analytic/MAIN_OBSERVED_PROGRAM_REVIEW_CONTROLS_V1.json', 'evidence/reviews/OBSERVED_PROGRAM.json')]
    for raw, relative in artifacts:
        copy(R / raw, relative)
    receipts = ['complete-io-model-v1', 'main-computed-globals-v1', 'main-io-trace-v1',
        'main-complete-model-v1', 'main-source-program-v1', 'main-observed-output-v1', 'main-observed-program-v1']
    for name in receipts:
        copy(R / 'research/analytic/work' / name / 'RECEIPT.json', 'evidence/original-host/' + name + '.json')
    payloads = []
    for name in ['original-output.bin', 'observed-total.bin']:
        p = B / 'evidence/observation' / name
        payloads.append(dict(path=str(p.relative_to(B)), bytes=p.stat().st_size, sha256=sha(p)))
    lock = dict(schema='COMPLETE_MAIN_OBSERVED_OUTPUT_SOURCE_EXTENSION_V1',
        compiler_sha256=original['compiler_sha256'], runtime_pins=original['runtime_pins'],
        generic_dependencies=original['generic_dependencies'],
        base_append_source_lock_sha256=sha(B / 'base/SOURCE_LOCK.json'),
        base_original_source_lock_sha256=sha(B / 'base/base/SOURCE_LOCK.json'),
        base_validator_lock_sha256=sha(B / 'base/REPRODUCER_LOCK.json'),
        base_source_modules=2272, base_theorem_roots=5613, sources=ordered, payloads=payloads,
        roots=roots, root_modules=[row['module'] for row in ordered],
        final_root='SynergyHeightC.MainObservedProgram.complete_source_main_observed_and_pnt',
        full_program_source_first_PV=False, combined_fresh_replay_completed=False,
        qualification='Prepared complete-main source/evidence extension. Actual source globals,768 input/point/budget/row executions, final128observedbytes,checked modeled flush/return and conditional ANT consumer. Complete fresh graph replay and final namespace isolation are not established by this input lock.')
    (B / 'SOURCE_LOCK.json').write_text(json.dumps(lock, indent=2) + '\n')
    provenance = dict(status='SOURCE_ONLY_COMPLETE_MAIN_EXTENSION_PREPARED_NOT_REPLAYED',
        prior_archive_sha256=sha(archive), base_modules=2272, added_modules=len(ordered),
        combined_modules=2272 + len(ordered), added_roots=len(roots),
        combined_distinct_roots=len(set(original['roots'] + append['roots'] + roots)),
        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), application_objects_read_or_copied=[],
        modeled_success_policy_not_universal_host_success=True,
        formal_observed_consumer_bytes=128, complete_raw_observation_bytes=98432)
    (B / 'PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps(provenance))

if __name__ == '__main__':
    main()
