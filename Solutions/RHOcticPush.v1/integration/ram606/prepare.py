#!/usr/bin/env python3
"""Freeze the actual606b synthesis and independent primary-source comparison proofs."""
from pathlib import Path
import hashlib, importlib.util, json, yaml

H = Path(__file__).resolve().parent
I, S = H.parent, H.parent.parent
R = S.parents[1]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

spec = importlib.util.spec_from_file_location(
    'source_header', R/'Solutions/RHLimit.v1/scripts/prepare_pi_manifest.py')
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
basis = {}
primary = read(I/'corrected/capture/SOURCE_CLOSURE.json')
for q in primary['baseline_manifests']:
    for row in read(R/q['path'])['modules']:
        need(row['module'] not in basis, 'basis collision')
        basis[row['module']] = row
previous = [primary, read(I/'supplement/audit-corrected-capture/SOURCE_CLOSURE.json'),
            read(S/'box/zero/cold-capture/SOURCE_CLOSURE.json'),
            read(I/'closed_box/capture/SOURCE_CLOSURE.json'),
            read(I/'spectral_final/capture/SOURCE_CLOSURE.json')]
for manifest in previous:
    for row in manifest['modules']:
        need(row['module'] not in basis, 'basis collision')
        basis[row['module']] = row
need(len(basis) == 712, 'exact accepted source712 foundation')
candidates, owned = {}, []

def add(module, path, own=False):
    path = Path(path)
    need(path.is_file() and module not in basis and module not in candidates,
         'source absent or duplicate:'+module)
    candidates[module] = {'module': module, 'original_path': str(path.relative_to(R)),
                          'sha256': sha(path)}
    if own:
        owned.append(module)

freeze = S/'ramanujan/signed-spectral/PROFILE_SOURCE_FREEZE.json'
scientific = read(freeze)
need(len(scientific['rows']) == 4, 'all4 accepted signed Ram science sources')
freezes = [freeze]
for row in scientific['rows']:
    path, receipt = R/row['file'], R/row['receipt']
    need(sha(path) == row['sha256'] and sha(receipt) == row['receipt_sha256'],
         'accepted source/receipt identity')
    result = read(receipt)
    need(result['status'] == 'PASS_DEV' and type(result['returncode']) is int
         and result['returncode'] == 0 and result['source_sha256'] == row['sha256'],
         'actual accepted scientific compiler route')
    add(path.stem, path, True)
for name in ['POSITIVE_INVERSE_SOURCE_FREEZE.json', 'PAIRED_INVERSE_SOURCE_FREEZE.json']:
    frozen = S/'comparisons'/name
    row = read(frozen)
    path, receipt = R/row['source'], R/row['receipt']
    need(sha(path) == row['sha256'], 'exact accepted comparison source')
    result = read(receipt)
    need(result['status'] == 'PASS_DEV' and type(result['returncode']) is int
         and result['returncode'] == 0 and result['source_sha256'] == row['sha256'],
         'actual accepted comparison compiler route')
    add(path.stem, path, True)
    freezes.append(frozen)
core = R/'IEANTN/Nodes/RamanujanGap/v6'
add('IEANTN.Nodes.RamanujanGap.v6.Conclusions', core/'Conclusions.lean')
add('Ram606Network', H/'Ram606Network.lean', True)
add('PublicRamanujanGapV6', R/'Solutions/RamanujanGap.v6/Solution.lean')
add('ExactRam606Types', H/'ExactRam606Types.lean', True)
meta = yaml.safe_load((core/'formalization.yaml').read_text())
final = []
for conclusion in meta['conclusions']:
    selected = [x for x in conclusion['justifications']
                if x['id'] == conclusion['designated']]
    need(len(selected) == 1 and selected[0]['kind'] == 'lean-noncompliant',
         'all new conclusions require actual proof')
    final.append(conclusion['challenge'])
need(len(final) == len(set(final)) == 7, 'exact7 new canonical roots')
types = read(H/'EXACT_TYPES.json')
need({x['declaration'] for x in types['claims']} == set(final), 'all exact typed consumers')
need(types['source_sha256'] == sha(H/'ExactRam606Types.lean'), 'exact-type source')
generic = {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq',
           'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Plausible'}
ordered, done, active = [], set(basis), set()

def visit(module):
    if module in done:
        return
    need(module in candidates and module not in active, 'missing/cyclic source:'+module)
    active.add(module)
    row = candidates[module]
    text = (R/row['original_path']).read_text()
    need('include_str' not in text and 'include_bin' not in text,
         'new resource requires explicit inventory')
    local, external = [], []
    for dep in reader.header_imports(text):
        need('.Challenge' not in dep, 'admitted Challenge in proof closure')
        if dep in basis or dep in candidates:
            visit(dep)
            local.append(dep)
        else:
            need(dep.split('.')[0] in generic, 'unmapped application edge:'+dep)
            external.append(dep)
    active.remove(module)
    done.add(module)
    ordered.append(dict(row, application_imports=local, generic_imports=external))

for module in candidates:
    visit(module)
need(len(ordered) == 10 and len(owned) == 8, 'complete new source scope')
out = H/'capture'
need(not out.exists(), 'immutable fresh capture required')
source = out/'frozen-source'
source.mkdir(parents=True)
for row in ordered:
    path = source/(row['module'].replace('.', '/')+'.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((R/row['original_path']).read_bytes())
    row['path'] = str(path.relative_to(R))
all_final = sorted(previous[-1]['final_roots']+final)
need(len(all_final) == len(set(all_final)) == 72, 'all72 canonical proof roots')
comparison_roots = ['RHOcticPush.ZeroComparison.positive_inverse_band',
                    'RHOcticPush.ZeroComparison.actual_both_sign_inverse_lower',
                    'RHOcticPush.ZeroComparison.excludes_both_sign_sixteen']
body_roots = all_final+['RHOcticPush.Network.fully_derived_box_network',
                       'RHOcticPush.Network.fully_derived_spectral_box_network',
                       'RHOcticPush.Network.fully_derived_spectral_ramanujan']+comparison_roots
template = (I/'spectral_final/capture/frozen-source/FinalSpectralAudit.lean').read_text()
start = template.index('    let mods := #[') if '    let mods := #[' in template else -1
# Reuse the independently reviewed generic environment/body audit, with an exact
# explicit module/root inventory; no source-name heuristic determines coverage.
import re
audit = template[template.index('open Lean Elab Command'):]
audit = re.sub(r'let mods := #\[[^\n]*\]',
               'let mods := #['+','.join(json.dumps(x) for x in owned)+']', audit)
audit = re.sub(r'let roots := #\[[^\n]*\]',
               'let roots := #['+','.join('`'+x for x in body_roots)+']', audit)
audit = audit.replace('RH_SPECTRAL_FINAL_', 'RH_RAM606_FINAL_')
audit = 'import Lean\nimport FinalSpectralAudit\n'+''.join(
    'import '+x['module']+'\n' for x in ordered)+'\n'+audit
path = source/'FinalRam606Audit.lean'
path.write_text(audit)
ordered.append({'module': 'FinalRam606Audit', 'original_path': None,
                'path': str(path.relative_to(R)), 'sha256': sha(path),
                'application_imports': ['FinalSpectralAudit']+
                                       [x['module'] for x in ordered],
                'generic_imports': ['Lean']})
manifest = {'schema': 'RH_RAM60611_SOURCE_CLOSURE_V1', 'foundation_modules': 712,
            'new_modules': 11, 'all_source_count': 723, 'owned_modules': owned,
            'modules': ordered, 'roots': [x['module'] for x in ordered],
            'final_roots': all_final, 'body_roots': body_roots,
            'comparison_roots': comparison_roots,
            'new_canonical_roots': sorted(final), 'literal_sources': [],
            'canonical_metadata': [{'path': str((core/'formalization.yaml').relative_to(R)),
                                    'sha256': sha(core/'formalization.yaml')}],
            'freezes': [{'path': str(x.relative_to(R)), 'sha256': sha(x)} for x in freezes],
            'selector_sha256': sha(__file__),
            'exact_type_inventory': {'path': str((H/'EXACT_TYPES.json').relative_to(R)),
                                     'sha256': sha(H/'EXACT_TYPES.json')},
            'source_claim': 'Ordinary kernel proofs. The local606..610 actual gap consumes '
                            'the actual v5 compensation profile plus three Buthe inputs; the '
                            'global overlay preserves all oldv5 profile and has old9 plus '
                            'general Perron/Nicolas=11 sources. No same-premise onset record. '
                            'Comparison checks only Lee-Nosal Eq10 as written, not final PNT. '
                            'No source-first PV or official Comparator claim.'}
(out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest, indent=2)+'\n')
print('captured11; all72 canonical roots;3combined+3comparison proof bodies')
