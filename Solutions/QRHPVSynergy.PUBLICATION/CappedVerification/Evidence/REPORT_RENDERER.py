"""Render the capped five-family session from a frozen, evidence-bound result record."""
from pathlib import Path
import argparse
import hashlib
import html
import importlib.util
import json
import math
import os
import re
from urllib.parse import urljoin, urlsplit

B = Path(__file__).resolve().parent
R = B.parents[1]
FAMILIES = {'height', 'mass', 'first moment', 'unpaired300', 'Gaussian basis'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        d = {}
        for k, v in items:
            need(k not in d, 'duplicate JSON key')
            d[k] = v
        return d
    def finite(number):
        value = float(number)
        need(math.isfinite(value), 'finite JSON number')
        return value
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def formula(body):
    return '<div class="formula" tabindex="0"><math xmlns="http://www.w3.org/1998/Math/MathML" display="block">'+body+'</math></div>'


def normalizations():
    pi = '<msub><mi>E</mi><mi>π</mi></msub><mo>(</mo><mi>x</mi><mo>)</mo>'
    psi = '<msub><mi>E</mi><mi>ψ</mi></msub><mo>(</mo><mi>x</mi><mo>)</mo>'
    li = '<msub><mi>Li</mi><mn>2</mn></msub><mo>(</mo><mi>x</mi><mo>)</mo>'
    power = '<msup><mi>x</mi><mrow><mo>−</mo><mfrac><mn>1</mn><mn>8</mn></mfrac></mrow></msup>'
    return formula(pi+'<mo>=</mo><mfrac><mrow><mo>|</mo><mi>π</mi><mo>(</mo><mi>x</mi><mo>)</mo><mo>−</mo>'+li+'<mo>|</mo></mrow><mfrac><mi>x</mi><mrow><mi>log</mi><mi>x</mi></mrow></mfrac></mfrac>') + formula(psi+'<mo>=</mo><mfrac><mrow><mo>|</mo><mi>ψ</mi><mo>(</mo><mi>x</mi><mo>)</mo><mo>−</mo><mi>x</mi><mo>|</mo></mrow><mi>x</mi></mfrac>') + formula('<mrow>'+pi+'<mo>≤</mo><mi>c</mi>'+power+'<mo>,</mo>'+psi+'<mo>≤</mo><mi>c</mi>'+power+'<mo>,</mo><mi>x</mi><mo>≥</mo><msup><mi>e</mi><mi>A</mi></msup></mrow>')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--data', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--evidence-base-url', required=True,
                    help='Immutable first publication commit; HTML is a later commit to avoid self-reference.')
    args = ap.parse_args()
    d = read(args.data)
    base = urlsplit(args.evidence_base_url)
    need(base.scheme == 'https' and base.netloc == 'raw.githubusercontent.com'
         and re.fullmatch(r'/hs-chae/IEANTN_test/[0-9a-f]{40}/Solutions/QRHPVSynergy[.]PUBLICATION/CappedVerification/', base.path)
         and not base.query and not base.fragment, 'immutable owner-repository evidence URL')
    need(d['schema'] == 1 and type(d['schema']) is int, 'exact result schema')
    need(d['status'] == 'FROZEN_CAPPED_SESSION_RESULTS_WITH_EXPLICIT_PENDING_GATES', 'frozen session result')
    need(d['all_session_jobs_drained'] is True, 'all own jobs stopped before final report')
    need(len(d['families']) == 5 and {x['name'] for x in d['families']} == FAMILIES,
         'exact owner-selected five families')
    need(d['mathematics_algorithms_and_assumptions_unchanged'] is True
         and d['new_exposure_or_optimization_experiments'] is False, 'fixed authorized scope')
    evidence_ids = set()
    for row in d['evidence']:
        need(type(row['id']) is str and row['id'] and row['id'] not in evidence_ids,
             'unique written evidence identity')
        evidence_ids.add(row['id'])
        p = (R/row['path']).resolve()
        need(p.is_relative_to(R) and p.is_file() and sha(p) == row['sha256'], 'actual source-bound report evidence')
    need(not args.out.exists(), 'fresh standalone report')
    esc = html.escape
    completed = sum(x['status'] == 'ACCEPTED_CORE_SOURCE_FIRST_CHAIN' for x in d['families'])
    if completed:
        core_row = next((x for x in d['evidence'] if x['id'] == 'core-five-family-acceptance'), None)
        need(core_row is not None, 'accepted family labels require the actual source-audit readback')
        core = read(R/core_row['path'])
        need(type(core['schema']) is int and core['schema'] == 1
             and core['status'] == 'PASS_FIVE_SELECTED_CORE_SOURCE_FIRST_CHAINS_ACTUAL_COMMON_NAMESPACE'
             and set(core['families']) == FAMILIES, 'exact completed common source-first acceptance schema')
        for item in d['families']:
            if item['status'] == 'ACCEPTED_CORE_SOURCE_FIRST_CHAIN':
                need('core-five-family-acceptance' in item['evidence_ids']
                     and core['families'][item['name']]['source_first_completion'] is True,
                     'family completion derives from actual pinned common auditors')
        need(core['families']['Gaussian basis']['acceptance_kind'] ==
             'closed_cap_provider_companion_consumed_by_verified_PNT_consumers',
             'Gaussian provider companion is not a standalone PNT root')
    title = 'Five numerical families: capped final verification'
    rows = ''
    for item in d['families']:
        need(type(item['evidence_ids']) is list and len(item['evidence_ids']) == len(set(item['evidence_ids']))
             and set(item['evidence_ids']) <= evidence_ids, 'every family cites actual unique evidence')
        need(item['status'] in {'ACCEPTED_CORE_SOURCE_FIRST_CHAIN', 'PENDING_FINAL_SOURCE_USE_ACCEPTANCE',
                               'FAILED_RETAINED_DIAGNOSTIC', 'INTERRUPTED_AT_SESSION_CAP'}, 'explicit family status')
        need(type(item['source_first_completion']) is bool
             and item['source_first_completion'] == (item['status'] == 'ACCEPTED_CORE_SOURCE_FIRST_CHAIN'),
             'source-first label agrees with actual family gate')
        if item['source_first_completion']:
            need(item['evidence_ids'] and item['old_type_preserved'] is True
                 and item['native_execution_axioms_remaining'] == [], 'accepted family complete evidence/type/native gates')
        references = ', '.join(esc(x) for x in item['evidence_ids'])
        rows += '<tr><th scope="row">'+esc(item['name'])+'</th><td>'+esc(item['role'])+'</td><td><strong>'+esc(item['display_status'])+'</strong><p>'+esc(item['explanation'])+'</p><p class="muted">Evidence: '+references+'</p></td></tr>'
    gates = ''.join('<tr><th>'+esc(x['name'])+'</th><td>'+esc(x['status'])+'</td><td>'+esc(x['meaning'])+'</td></tr>' for x in d['gates'])
    resources = ''
    def gib(x): return 'unavailable' if x is None else f'{x/2**30:.3f}'
    for item in d['resources']:
        resources += '<tr><td>'+esc(item['label'])+'</td><td>'+str(item['exit_code'])+'</td><td>'+f'{item["elapsed_seconds"]:.2f}'+'</td><td>'+gib(item['RAM_limit_bytes'])+'</td><td>'+('≥ '+gib(item['sampled_charged_RAM_lower_bound_bytes']) if item['sampled_charged_RAM_lower_bound_bytes'] is not None else 'unavailable')+'</td><td>'+esc(item['OOM_classification'])+'</td></tr>'
    pending = ''.join('<li>'+esc(x)+'</li>' for x in d['pending']) or '<li>No remaining local obligation in the declared acceptance scope. Official network registration remains separate.</li>'
    failures = ''.join('<li>'+esc(x)+'</li>' for x in d['failures_and_limitations']) or '<li>No unexpected failure was observed in the attempted session stages. Expected negative controls remain separate.</li>'
    overlay = d['reproduction_overlay']
    need(re.fullmatch(r'[A-Z0-9_]+[.]tar[.]xz', overlay['filename']) is not None
         and type(overlay['bytes']) is int and overlay['bytes'] > 0
         and type(overlay['master_version']) is int and overlay['master_version'] >= 6
         and type(overlay['control_cases']) is int and overlay['control_cases'] > 0
         and overlay['full_default_executed'] is False
         and overlay['full_final283_clean_replay_complete'] is False
         and overlay['standalone_archive_apply_input_checks_passed'] is True,
         'actual corrected overlay identity and qualified execution status')
    overlay_blurb = ('<p><strong>Source/control snapshot; complete clean replay remains unfinished.</strong> '
        '<a href="'+esc(overlay['filename'])+'">download the '+format(overlay['bytes'], ',')+'-byte overlay</a> '
        'and read the <a href="README.md">exact replay instructions and known stopping point</a>. '
        'The preserved original archive’s unexecuted v3 default had control-path, wall-limit and partial-import-view defects. '
        'The additive correction selects the reviewed metadata exporter and master v'+str(overlay['master_version'])+
        '; mathematical and numerical inputs remain unchanged. Actual archive extraction, overlay application and input checks passed, '
        'along with all '+str(overlay['control_cases'])+' relocated controls. '
        'The full default still stops at the final283 typed-index stage: a clean, parameterized producer/checkpoint/audit/seal hook '
        'for the 26 existing kernel-baseline roots is not yet implemented and tested. '
        'The actual host verification receipts remain valid, but this snapshot is not a completed end-to-end reproduction procedure.</p>')
    css = '''*{box-sizing:border-box}body{margin:0;background:#f3f5f8;color:#182637;font:16px/1.58 system-ui,sans-serif}main{max-width:1050px;margin:auto;padding:30px 19px 60px}h1{font-size:clamp(1.9rem,4.7vw,2.7rem);line-height:1.18}h2{font-size:1.4rem;margin-top:0}h3{font-size:1.1rem}p{max-width:88ch;overflow-wrap:anywhere}.card{background:white;border:1px solid #d8e1ec;border-radius:12px;padding:22px;margin:20px 0}.status{border-left:6px solid #315f93}.good{color:#14633e}.pending{color:#965412}nav{display:flex;gap:8px;flex-wrap:wrap;margin:22px 0}nav a{padding:7px 11px;border:1px solid #bdcbdc;border-radius:6px;background:white;text-decoration:none}a{color:#17599a}.scroll,.formula{overflow-x:auto;max-width:100%}.formula{padding:14px 6px;margin:14px 0;border:1px solid #d7e0eb;border-radius:8px}.scroll:focus-visible,.formula:focus-visible,a:focus-visible,summary:focus-visible{outline:3px solid #a36219;outline-offset:3px}table{border-collapse:collapse;width:100%;font-size:.94rem}td,th{border-bottom:1px solid #dbe4ee;padding:11px 9px;text-align:left;vertical-align:top}th{background:#f1f5fa}td p{margin:.4em 0}.muted{color:#55667a;font-size:.93rem}code{font-size:.82rem;overflow-wrap:anywhere}summary{cursor:pointer;font-weight:700}.metric{display:inline-block;margin:0 25px 10px 0}.metric strong{display:block;font-size:1.7rem}@media(max-width:600px){main{padding:22px 12px 44px}.card{padding:17px 13px}table{font-size:.88rem}td,th{padding:9px 7px}nav a{font-size:.9rem}}'''
    page = f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{title}</title><style>{css}</style></head><body><main>
<p class="muted">IEANTN · fixed source-first verification session · 17 November 2026 UTC</p><h1>{title}</h1>
<nav aria-label="Report sections"><a href="#outcome">Outcome</a><a href="#families">Five families</a><a href="#math">Mathematics</a><a href="#gates">Verification gates</a><a href="#trust">Trust</a><a href="#resources">Resources</a><a href="#remaining">Remaining work</a><a href="#reproduce">Reproduce</a></nav>
<section class="card status" id="outcome"><h2>{esc(d['headline'])}</h2><div class="metric"><strong>{completed}/5</strong>core source-first family chains accepted</div><div class="metric"><strong>{esc(d['session_elapsed_display'])}</strong>session wall time</div><p>{esc(d['outcome_summary'])}</p><p><strong>All session jobs have stopped.</strong> No broad exposure experiment, numerical optimization, mathematical assumption change or whole-IEANTN completion campaign was started.</p><p class="muted">Budget: start {esc(d['started_utc'])}; proof-work cutoff {esc(d['proof_cutoff_utc'])}; hard deadline {esc(d['deadline_utc'])}. Actual stop: {esc(d['stopped_utc'])}. A passed build, a source-first consumer proof and an official network verification receipt are separate evidence.</p></section>
<section class="card" id="families"><h2>The exact five families</h2><p>The scope is height, mass, first moment, unpaired-300 and Gaussian basis. Their outputs compose; they are not five independent discoveries or every unfinished numerical program in IEANTN.</p><div class="scroll" tabindex="0"><table><tr><th>Family</th><th>Mathematical role</th><th>Actual acceptance and limit</th></tr>{rows}</table></div><p>The actual C/C++ numerical runs and their source/build/output associations predate this capped session and remain pinned evidence. This session checks their source-first proof connections and final consumers; it does not claim fresh native numerical executions.</p><p>Program sources and numerical inputs are frozen. The actual native-input manifest and the formal source-binding/consumer identities are recorded separately. A 24-byte translation-unit wrapper containing an include directive is not the complete identity of its included program.</p></section>
<section class="card" id="math"><h2>Preserved conditional mathematical results</h2><p>The prime-counting and Chebyshev error normalizations remain unchanged. The logarithmic integral begins at two.</p>{normalizations()}<p>On the corresponding domains, the complete local mathematical consumer proofs establish:</p><div class="scroll" tabindex="0"><table><tr><th>Route</th><th>Coefficient c</th><th>Logarithmic onset A</th></tr><tr><td>Mass + first moment + earlier analytic transfer</td><td>0.009963192</td><td>240</td></tr><tr><td>Unpaired-300 source output</td><td>0.008732871</td><td>300</td></tr><tr><td>Paired height + mass composition</td><td>0.007984699</td><td>400</td></tr></table></div><p>These remain conditional on the same fourteen analytic/finite-RH/open-QRH inputs. Finite RH is not raised beyond its original height. The open seven-eighths zero-free half-plane excludes the pole at one and makes no boundary assertion. The separate OpenAI formalization is not silently imported into this toolchain.</p><p>The coefficient/range trade-offs and retained whole-function portfolio are preserved. No optimality, best-known or universal PV-superiority claim is made. The separate five-root comparison and the prime-rich consequence retain their own evidence status in the gates below.</p></section>
<section class="card" id="gates"><h2>What was actually checked</h2><p>The starting source-built chain already contained 14,878 modules: 10,970 explicitly validated original modules and 3,908 fresh research modules, with 20,541 selected typed roots. This session reuses that accepted parent. It is not another empty-application-bank run.</p><div class="scroll" tabindex="0"><table><tr><th>Gate</th><th>Recorded status</th><th>Meaning</th></tr>{gates}</table></div><p>The full research inventory has 283 written entries: 250 source-backed or generic propositions, 32 intentional kernel-only baselines and one unchanged data definition. These are not 283 source-first PV programs. The representative family-to-consumer list does not replace that full inventory.</p></section>
<section class="card" id="trust"><h2>Source-first verification and remaining trust</h2><p>PV means actual executable C/C++ source connected to its formal AST/execution model, relevant arithmetic/safety facts, justified numerical output, and actual theorem consumption. Native observation, untrusted witness generation, kernel-only numerical checking and ordinary certificate checking have distinct roles.</p><p>The newer five-family numerical code uses bounded unsigned 512-bit words with 128 fractional bits. The earlier original Scoped Winner C++ evaluator implements its own interval arithmetic using the pinned core Nat/reference-count runtime API. It does not call a Lean application evaluator. Its unchanged original migration is a separate completed result.</p><p>The pinned Lean kernel, standard axioms, C/C++ compiler/ABI, generic runtime and documented arithmetic/I/O/OS/hardware contracts remain explicit. Application initialization, loops, guards, ownership and same-output consumption belong to the application proofs; successful application output is not trusted as a generic platform fact. Modeled accepted I/O bytes and actual source/build/native-stdout association remain distinct checks.</p><p>The Lean <code>#eval</code> proposal utility is untrusted witness generation. It is not PV authority. Ordinary kernel checking of the actual C execution and consumer proofs provides the mathematical acceptance. Local Comparator/NanoDa and official network registration are reported separately; no receipt or verified node status is invented.</p></section>
<section class="card" id="resources"><h2>Actual session resources</h2><p>The study uses at most 300 GiB aggregate RAM and 300 GiB aggregate scratch, with actual available RAM and free disk checked independently and host reserves protected. No obsolete 4 GiB cap was imposed on numerical/proof work. Small metadata stages have smaller justified limits.</p><details><summary>Show every recorded resource scope, including failed attempts</summary><div class="scroll" tabindex="0"><table><tr><th>Stage</th><th>Exit</th><th>Seconds</th><th>RAM allowance GiB</th><th>Sampled charged RAM GiB</th><th>OOM evidence</th></tr>{resources}</table></div></details><p>{esc(d['child_RSS_summary'])} <a href="Evidence/FOUR_CONTEXT_SOURCE_RSS_MEASUREMENTS_V1.json">Exact per-command RSS evidence</a>.</p><p>Sampled charged RAM is a lower bound. The exact cgroup peak was unavailable; child RSS is a separate process measure. Recorded workspace disk samples are aggregate allocation, not exclusive per-run peak disk. Overlapping phases and shared source-built modules must not be added as independent costs or discoveries.</p></section>
<section class="card" id="remaining"><h2>Failures, limits and remaining work</h2><ul>{failures}</ul><h3>Pending after this stop</h3><ul>{pending}</ul><p>No later proof completion rescored the historical 192 exposure sessions or the six-session follow-up. Their primary outcomes remain unchanged. This session tests validity and connected verification of fixed existing results, not optimality or exposure effectiveness.</p></section>
<section class="card" id="reproduce"><h2>Evidence, reproduction and pause</h2><p><a href="EVIDENCE.tar.gz">Download this session’s essential evidence and source deltas</a> · <a href="Evidence/FINAL_REPORT_DATA.json">Exact result record</a> · <a href="Evidence/ARTIFACT_IDENTITIES.json">Artifact hashes</a> · <a href="../QRH_SOURCE_FIRST_RESEARCH_REPRODUCTION_20261116.tar.xz">Full clean source-reproduction package</a>.</p>{overlay_blurb}<p>The clean source package includes exact C/C++ source, deterministic numerical generators, fixed parameters and dependency commits, original source/evidence package, source-only compilation and context/network consumers. No application object bank is distributed. The complete monolithic convenience default remains unexecuted as another uninterrupted run; actually completed components and source-built continuations have separate receipts.</p><p>Only verified-regenerable experiment-owned temporary data may be removed. Accepted proof sources, essential receipts, original inputs and the only reproducibility copies remain preserved. All pending stages have exact restart notes; none is left executing after this report.</p><p class="muted">Long equations and tables scroll horizontally. Focus a panel and use the arrow keys, or swipe on a narrow screen. This standalone HTML embeds its math font and license and needs no scripts, browser extension or CDN.</p></section></main></body></html>'''
    page = re.sub(r'href="([^"#][^"]*)"',
                  lambda match: 'href="'+esc(urljoin(args.evidence_base_url, html.unescape(match.group(1))), quote=True)+'"'
                  if not urlsplit(html.unescape(match.group(1))).scheme else match.group(0), page)
    font_file = R/'reports/final-campaign-v1/math-font-v1/embed_math_font.py'
    spec = importlib.util.spec_from_file_location('reviewed_math_font', font_file)
    font = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(font)
    page = font.embed(page)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(page)
    print('CAPPED_REPORT_RENDERED', sha(args.out), 'families accepted', completed)


if __name__ == '__main__':
    main()
