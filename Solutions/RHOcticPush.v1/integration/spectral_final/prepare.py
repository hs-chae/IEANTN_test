#!/usr/bin/env python3
"""Freeze the actual signed spectral proof and its complete new network consumers."""
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
            read(I/'closed_box/capture/SOURCE_CLOSURE.json')]
for manifest in previous:
    for row in manifest['modules']:
        need(row['module'] not in basis, 'basis collision')
        basis[row['module']] = row
need(len(basis) == 693, 'exact accepted source693 foundation')
candidates, owned = {}, []

def add(module, path, own=False):
    path = Path(path)
    need(path.is_file() and module not in basis and module not in candidates,
         'source absent or duplicate:'+module)
    candidates[module] = {'module': module, 'original_path': str(path.relative_to(R)),
                          'sha256': sha(path)}
    if own:
        owned.append(module)

freeze = S/'spectral-076/SOURCE_FREEZE.json'
scientific = read(freeze)
need(len(scientific['modules']) == 14, 'all14 accepted spectral science sources')
for row in scientific['modules']:
    path, receipt = R/row['path'], R/row['receipt']
    need(sha(path) == row['sha256'] and sha(receipt) == row['receipt_sha256'],
         'accepted source/receipt identity')
    result = read(receipt)
    need(result['status'] == 'PASS_DEV' and type(result['returncode']) is int
         and result['returncode'] == 0 and result['source_sha256'] == row['sha256'],
         'actual accepted scientific compiler route')
    add(row['module'], path, True)
core = R/'IEANTN/Nodes/RHPrimeCounting/v5'
add('IEANTN.Nodes.RHPrimeCounting.v5.Conclusions', core/'Conclusions.lean')
add('SpectralNetwork', H/'SpectralNetwork.lean', True)
add('PublicRHPrimeCountingV5', R/'Solutions/RHPrimeCounting.v5/Solution.lean')
add('ExactSpectralTypes', H/'ExactSpectralTypes.lean', True)
meta = yaml.safe_load((core/'formalization.yaml').read_text())
final = []
for conclusion in meta['conclusions']:
    selected = [x for x in conclusion['justifications']
                if x['id'] == conclusion['designated']]
    need(len(selected) == 1 and selected[0]['kind'] == 'lean-noncompliant',
         'all new conclusions require actual proof')
    final.append(conclusion['challenge'])
need(len(final) == len(set(final)) == 10, 'exact10 new canonical roots')
types = read(H/'EXACT_TYPES.json')
need({x['declaration'] for x in types['claims']} == set(final), 'all exact typed consumers')
need(types['source_sha256'] == sha(H/'ExactSpectralTypes.lean'), 'exact-type source')
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
need(len(ordered) == 18 and len(owned) == 16, 'complete new source scope')
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
need(len(all_final) == len(set(all_final)) == 65, 'all65 canonical proof roots')
body_roots = all_final+['RHOcticPush.Network.fully_derived_box_network',
                       'RHOcticPush.Network.fully_derived_spectral_box_network']
template = (I/'closed_box/capture/frozen-source/FinalClosedBoxAudit.lean').read_text()
start = template.index('    let mods := #[') if '    let mods := #[' in template else -1
# Reuse the independently reviewed generic environment/body audit, with an exact
# explicit module/root inventory; no source-name heuristic determines coverage.
import re
audit = template[template.index('open Lean Elab Command'):]
audit = re.sub(r'let mods := #\[[^\n]*\]',
               'let mods := #['+','.join(json.dumps(x) for x in owned)+']', audit)
audit = re.sub(r'let roots := #\[[^\n]*\]',
               'let roots := #['+','.join('`'+x for x in body_roots)+']', audit)
audit = audit.replace('RH_CLOSED_BOX_', 'RH_SPECTRAL_FINAL_')
audit = 'import Lean\nimport FinalClosedBoxAudit\n'+''.join(
    'import '+x['module']+'\n' for x in ordered)+'\n'+audit
path = source/'FinalSpectralAudit.lean'
path.write_text(audit)
ordered.append({'module': 'FinalSpectralAudit', 'original_path': None,
                'path': str(path.relative_to(R)), 'sha256': sha(path),
                'application_imports': ['FinalClosedBoxAudit']+
                                       [x['module'] for x in ordered],
                'generic_imports': ['Lean']})
manifest = {'schema': 'RH_SPECTRAL19_SOURCE_CLOSURE_V1', 'foundation_modules': 693,
            'new_modules': 19, 'all_source_count': 712, 'owned_modules': owned,
            'modules': ordered, 'roots': [x['module'] for x in ordered],
            'final_roots': all_final, 'body_roots': body_roots,
            'new_canonical_roots': sorted(final), 'literal_sources': [],
            'canonical_metadata': [{'path': str((core/'formalization.yaml').relative_to(R)),
                                    'sha256': sha(core/'formalization.yaml')}],
            'freezes': [{'path': str(freeze.relative_to(R)), 'sha256': sha(freeze)}],
            'selector_sha256': sha(__file__),
            'exact_type_inventory': {'path': str((H/'EXACT_TYPES.json').relative_to(R)),
                                     'sha256': sha(H/'EXACT_TYPES.json')},
            'source_claim': 'Ordinary kernel proofs. General published Perron/Nicolas remain '
                            'explicit B-tier sources. Full Box pi needs RH/Perron/Nicolas/BPT, '
                            'with no old GM or Buthe psi/J sources. CH retains its old psi premise. '
                            'No source-first PV or official Comparator claim.'}
(out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest, indent=2)+'\n')
print('captured19; all65 canonical roots; both actual combined proof bodies')
