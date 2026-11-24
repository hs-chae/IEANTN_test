#!/usr/bin/env python3
"""Read-only final delta review; never executes the numerical certifier or mutates Git."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib
import json
import re
import subprocess

D = Path('/data/ivy-rh-one-prime-20261124')
R = D / 'network'
S = R / 'Solutions/RHOnePrimeEvolution.v1'
HERE = Path(__file__).resolve().parent
REV = '109729571ac5e6ea38944c965abad11a8dad4d43'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def identity(p):
    return {'file': str(p), 'bytes': p.stat().st_size, 'sha256': sha(p)}

def load(p):
    return json.loads(p.read_text())

candidate = S / 'gaussian_kernel/CANDIDATE_DEGREE12.json'
saved = D / 'gaussian-kernel/degree12-arb/RESULT.json'
copy = S / 'gaussian_kernel/evidence/MATCHED_A36OVER11_DEGREE12_ARB_RESULT.json'
script = S / 'analytic/certify_gaussian_objective.py'
actual = S / 'gaussian_kernel/GaussianSources.lean'
frozen = D / 'gaussian-kernel/full-reproduce01/lean/source/GaussianSources.lean'
sidecar = S / 'gaussian_kernel/EXTERNAL_ARB_IDENTITY_AUDIT.json'
c, e = load(candidate), load(saved)
require(saved.read_bytes() == copy.read_bytes(), 'saved/copy receipt bytes differ')
require(sha(candidate) == e['candidate_sha256'], 'candidate hash mismatch')
require(sha(script) == e['script_sha256'], 'script hash mismatch')
require(actual.read_bytes() == frozen.read_bytes(), 'actual/frozen numerical source differs')
require(c['degree'] == e['degree'] == 12 and e['A'] == '36/11', 'wrong degree/penalty')
require(e['parameters'] == {'precision_bits': 256, 'root_digits': 45}, 'wrong precision/root parameters')
coeff = list(map(F, c['coefficients_decimal_exact_rationals']))
require(len(coeff) == 13 and coeff == list(map(F, e['exact_coefficients_decimal'])), '13 coefficient identity failed')

def binom(q, n):
    value = F(1)
    for j in range(n):
        value *= q - j
    return value / factorial(n)

polynomials = {}
for name, sign in [('P', 1), ('Q', -1)]:
    # Independent rational coefficient formula for L_n^(-1/2)(2v).
    values = [sum((sign ** n * coeff[n] * (-1) ** k *
                   binom(F(n) - F(1, 2), n-k) * 2**k / factorial(k)
                   for n in range(k, 13)), F(0)) for k in range(13)]
    require(values == list(map(F, e[name]['polynomial_low_to_high_coeffs'])), 'independent Laguerre formula differs: ' + name)
    decl = 'normSource' if name == 'P' else 'wingSource'
    body = re.search(r'def ' + decl + r' : List ℚ := \[(.*?)\]', actual.read_text(), re.S)
    require(body is not None, 'missing actual coefficient declaration')
    actual_values = [F(int(a), int(b)) for a, b in re.findall(r'\((-?\d+)/(\d+) : ℚ\)', body.group(1))]
    expanded = [values[j//2] if j % 2 == 0 else F(0) for j in range(25)]
    require(actual_values == expanded, 'actual 25-position source differs: ' + decl)
    polynomials[decl] = {'laguerre_coefficients': 13, 'actual_positions': 25,
                          'independent_formula_and_receipt_match': True}

require(sorted(p.name for p in saved.parent.iterdir()) == ['RESULT.json'], 'new run provenance files need review')
preview = D / 'PUBLICATION_PREVIEW_V2.json'
p = load(preview)
require(sha(preview) == '49044223bbf85f940789fb2da08fb5e76695ee8026b27f40e50daf9929b5aaaa', 'preview mutated')
selected = p['selected_files']
require(len(selected) == 868, 'publication selection count changed')
paths = [x['path'] for x in selected]
require(len(set(paths)) == len(paths), 'duplicate selected path')
changed = subprocess.run(['git', 'diff-tree', '--no-commit-id', '--name-only', '-r', REV],
                         cwd=R, check=True, capture_output=True).stdout.decode().splitlines()
require(not (set(changed) - set(paths)), 'unreviewed committed path')
requests = ''.join(REV + ':' + path + '\n' for path in paths).encode()
blob = subprocess.run(['git', 'cat-file', '--batch'], input=requests, cwd=R,
                      check=True, capture_output=True).stdout
pos = 0
for row in selected:
    end = blob.index(b'\n', pos)
    header = blob[pos:end].split()
    require(len(header) == 3 and header[1] == b'blob', 'missing committed blob')
    size = int(header[2])
    start = end + 1
    data = blob[start:start+size]
    require(size == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
            'committed preview blob differs: ' + row['path'])
    require(blob[start+size:start+size+1] == b'\n', 'bad batch framing')
    pos = start + size + 1
require(pos == len(blob), 'unconsumed blob output')

pin = load(S / 'SOURCE_PIN.json')
build = load(S / 'reports/REPORT_BUILD.json')
require(pin['commit'] == build['source_revision'] == REV, 'report/source pin mismatch')
math_receipt = HERE / 'FINAL_RENDERED_MATH_V3.json'
math = load(math_receipt)
require(math['status'] == 'PASS_EXACT_RENDERED_MATHML_SOURCE_ASSOCIATION', 'final rendered gate failed')
require([x['formula_count'] for x in math['reports']] == [52, 52, 67, 67, 8], 'formula count changed')
for row in math['reports']:
    require(sha(Path(row['file'])) == row['sha256'], 'report mutated after MathML review')
for row in math['inputs']:
    require(sha(Path(row['file'])) == row['sha256'], 'renderer input mutated after MathML review')
require(sha(Path(math['build_receipt']['file'])) == math['build_receipt']['sha256'], 'build receipt mutated')

matrix = S / 'HEADLINE_MATRIX.json'
rows = load(matrix)['rows']
require(len(rows) == 30, 'canonical matrix count changed')
for row in rows:
    for prefix in ['', 'proof_']:
        source = R / row[prefix+'file']
        require(sha(source) == row[prefix+'sha256' if prefix else 'source_sha256'], 'matrix source hash mismatch')
        line = row[prefix+'line']
        name = row[prefix+'declaration'].rsplit('.', 1)[-1]
        require(name in source.read_text().splitlines()[line-1], 'matrix declaration/line mismatch: ' + name)

scroll = D / 'artifact-checks/table-scroll-final-fix-v1/RESULT.json'
gate = load(scroll)
for row in gate['rows']:
    require(sha(S/'reports'/row['report']) == row['after_sha256'], 'scroll gate/current report mismatch')
    require(all(row[key] for key in ['prose_byte_identical', 'all_MathML_byte_identical',
                                    'links_byte_identical', 'CSS_byte_identical',
                                    'only_network_mechanism_table_wrapper_added']), 'non-presentation delta')

result = {
  'status': 'PASS_FINAL_SOURCE_MATH_FIDELITY_DELTA_NO_MATERIAL_ISSUE',
  'reviewer': '/root/count_frontier',
  'scope': 'Final five reports, 30-row typed theorem matrix, recovered matching degree12 Arb evidence and bounded publication inclusion delta. Not a global source census, optimality or legal/privacy guarantee.',
  'source_revision': REV,
  'source_pin': identity(S/'SOURCE_PIN.json'),
  'final_rendered_math': identity(math_receipt),
  'reports': math['reports'],
  'matrix': identity(matrix),
  'matrix_rows': 30,
  'new_evidence': {
    'actual_report': 'reports/oneprime_sections.py:49; reports/gaussian_sections.py:128 and the final rendered five reports',
    'recoverable_original_claim': 'The independently matched saved result records A=36/11, the actual 13 rational Laguerre coefficients, exact P/Q coefficients, 256-bit directed Arb/exact Sturm output and inverse J=[0.834009630792697113750888875097982283910636 +/- 4.37e-43].',
    'saved_result': identity(saved), 'preserved_result': identity(copy),
    'candidate': identity(candidate), 'certifier': identity(script),
    'actual_lean_numerical_source': identity(actual), 'identity_sidecar': identity(sidecar),
    'independent_exact_coefficient_checks': polynomials,
    'missing_detail_and_impact': 'The result directory preserves only RESULT.json, not raw argv, separate contemporaneous stdout/stderr or OS exit receipt. The command is reconstructed. The saved matching enclosure remains external E; it does not replace the kernel-proved D <=0.834021 theorem or establish source-first PV.',
    'classification': 'External directed Arb/Sturm E with matching mathematical input and incomplete historical execution provenance; no new numerical execution performed.',
    'earlier_selection_correction': 'The earlier review selected analytic/ evidence and omitted gaussian-kernel/degree12-arb. Its A4/different-candidate mismatch was real, but any whole-campaign absence inference was too broad. This expanded selection supersedes that inference while preserving every earlier review and original outcome.',
    'current_report_judgment': 'The historical approximate SciPy row is retained honestly; the separately matched directed E receipt and missing execution record are disclosed. No denial of the recovered receipt, no promotion to D/PV, no change to the proved mathematical theorem.'
  },
  'preserved_prior_reviews': [identity(S/'gaussian_fourier/reviews/FinalReports_v1/REVIEW.json'),
                            identity(S/'gaussian_fourier/reviews/CMSFunctionalBridge_v1/REVIEW.json')],
  'publication_preview': {
    'preview': identity(preview), 'selected_files': 868,
    'actual_changed_commit_paths': len(changed),
    'unexpected_changed_paths': 0, 'committed_blob_hash_mismatches': 0,
    'selection_notes': '613 selected paths were unchanged inherited dependencies; all 868 committed blobs checked against this exact preview, rather than assuming every selected file is new.',
    'bounded_content_review': 'No obvious private, unlicensed or irrelevant inclusion found in the actual preview. No prompt/transcript/memory/credentials/environment/cache directory selection. Nicely PDF explicitly public domain; LeanCert copied sources retain copyright/Apache-2 notices; compiler-log ZIP member names checked. This is bounded inclusion review, not an exhaustive legal/privacy guarantee.'
  },
  'presentation_delta': {'scroll_wrapper_gate': identity(scroll),
                         'judgment': 'Only an existing tablewrap/tabindex wrapper was added to the two network mechanism tables; actual prose, MathML, source links and CSS are byte-identical to the preceding reviewed version. Browser delivery/phone gates are separate.'},
  'remaining_trust_and_limits': 'New numerical/Fourier/consumer proofs are kernel-only D with standard Lean axioms, not source-first PV. CMS analytic input is explicit literature-backed B. No explicit onset follows from the new asymptotic Gaussian theorem; no best-known or optimality claim. Historical global metadata receipt provenance failure remains separate and is not a source/math success claim.'
}
out = HERE / 'REVIEW.json'
require(not out.exists(), 'immutable REVIEW.json already exists')
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'review': str(out), 'sha256': sha(out),
                  'reports': len(math['reports']), 'matrix_rows': len(rows),
                  'committed_blobs_checked': len(selected), 'changed_paths': len(changed)}))
