#!/usr/bin/env python3
"""Freeze complete prime-square feedback and exact canonical typed consumers."""
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
            read(I/'spectral_final/capture/SOURCE_CLOSURE.json'),
            read(I/'ram606/capture/SOURCE_CLOSURE.json')]
for manifest in previous:
    for row in manifest['modules']:
        need(row['module'] not in basis, 'basis collision')
        basis[row['module']] = row
need(len(basis) == 723, 'exact accepted source723 foundation')
candidates, owned = {}, []

def add(module, path, own=False):
    path = Path(path)
    need(path.is_file() and module not in basis and module not in candidates,
         'source absent or duplicate:'+module)
    candidates[module] = {'module': module, 'original_path': str(path.relative_to(R)),
                          'sha256': sha(path)}
    if own:
        owned.append(module)

freezes = []
for directory, count in [('corollary',2),('feedback',4)]:
    freeze = S/'spectral-076'/directory/'SOURCE_FREEZE.json'
    scientific = read(freeze)
    need(len(scientific['modules'])==count,'all exact accepted sources')
    freezes.append(freeze)
    for row in scientific['modules']:
        path, receipt = R/row['path'], R/row['receipt']
        need(sha(path)==row['sha256'] and sha(receipt)==row['receipt_sha256'],
             'accepted scientific source and receipt')
        result=read(receipt)
        need(result['status']=='PASS_DEV' and type(result['returncode']) is int
             and result['returncode']==0 and result['source_sha256']==row['sha256'],
             'accepted actual scientific compilation')
        add(row['module'],path,True)
core = R/'IEANTN/Nodes/RHPrimeCounting/v6'
add('IEANTN.Nodes.RHPrimeCounting.v6.Conclusions', core/'Conclusions.lean', True)
add('FeedbackNetwork', H/'FeedbackNetwork.lean', True)
add('PublicRHPrimeCountingV6', R/'Solutions/RHPrimeCounting.v6/Solution.lean')
add('ExactFeedbackTypes', H/'ExactFeedbackTypes.lean', True)
meta = yaml.safe_load((core/'formalization.yaml').read_text())
final = []
for conclusion in meta['conclusions']:
    selected = [x for x in conclusion['justifications']
                if x['id'] == conclusion['designated']]
    need(len(selected) == 1 and selected[0]['kind'] == 'lean-noncompliant',
         'all new conclusions require actual proof')
    final.append(conclusion['challenge'])
need(len(final) == len(set(final)) == 11, 'exact11 new canonical roots')
types = read(H/'EXACT_TYPES.json')
need({x['declaration'] for x in types['claims']} == set(final), 'all exact typed consumers')
need(types['source_sha256'] == sha(H/'ExactFeedbackTypes.lean'), 'exact-type source')
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
need(len(ordered) == 10 and len(owned) == 9, 'complete new source scope')
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
need(len(all_final) == len(set(all_final)) == 83, 'all83 canonical proof roots')
comparison_roots = ['RHOcticPush.ZeroComparison.positive_inverse_band',
                    'RHOcticPush.ZeroComparison.actual_both_sign_inverse_lower',
                    'RHOcticPush.ZeroComparison.excludes_both_sign_sixteen']
body_roots = all_final+['RHOcticPush.Network.fully_derived_box_network',
                       'RHOcticPush.Network.fully_derived_spectral_box_network',
                       'RHOcticPush.Network.fully_derived_spectral_ramanujan',
                       'RHOcticPush.Network.fully_derived_feedback_box_network']+comparison_roots
template = (I/'ram606/capture/frozen-source/FinalRam606Audit.lean').read_text()
start = template.index('    let mods := #[') if '    let mods := #[' in template else -1
# Reuse the independently reviewed generic environment/body audit, with an exact
# explicit module/root inventory; no source-name heuristic determines coverage.
import re
audit = template[template.index('open Lean Elab Command'):]
audit = re.sub(r'let mods := #\[[^\n]*\]',
               'let mods := #['+','.join(json.dumps(x) for x in owned)+']', audit)
audit = re.sub(r'let roots := #\[[^\n]*\]',
               'let roots := #['+','.join('`'+x for x in body_roots)+']', audit)
audit = audit.replace('RH_RAM606_FINAL_', 'RH_FEEDBACK_FINAL_')
audit = 'import Lean\nimport FinalRam606Audit\n'+''.join(
    'import '+x['module']+'\n' for x in ordered)+'\n'+audit
path = source/'FinalFeedbackAudit.lean'
path.write_text(audit)
ordered.append({'module': 'FinalFeedbackAudit', 'original_path': None,
                'path': str(path.relative_to(R)), 'sha256': sha(path),
                'application_imports': ['FinalRam606Audit']+
                                       [x['module'] for x in ordered],
                'generic_imports': ['Lean']})
manifest = {'schema': 'RH_FEEDBACK11_SOURCE_CLOSURE_V1', 'foundation_modules': 723,
            'new_modules': 11, 'all_source_count': 734, 'owned_modules': owned,
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
            'source_claim': 'Ordinary kernel proofs, not source-first PV. The same four explicit '
                            'RH/generalPerron/Nicolas/BPT source providers construct actual J_upper '
                            'then actual prime-power correction, then ordinary pi and interval counts. '
                            'Full raw lower-scale J, min70, entire35-ray preservation and strict whole '
                            'gain are retained. The .42 scalar bound is a corollary, not optimality '
                            'or a best-known claim. No official Comparator receipt is asserted.'}
(out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest, indent=2)+'\n')
print('captured11; all83 canonical roots;4combined+3comparison proof bodies')
