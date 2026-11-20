#!/usr/bin/env python3
"""Combine the detailed report, accepted local alternative and bounded controls."""
from pathlib import Path
import argparse
import hashlib
import html
import json
import math

S = Path(__file__).resolve().parents[1]


def need(value, message):
    if not value:
        raise ValueError(message)


def read_json(path):
    def pairs(items):
        value = {}
        for key, item in items:
            need(key not in value, 'duplicate JSON key: ' + key)
            value[key] = item
        return value

    def number(raw):
        value = float(raw)
        need(math.isfinite(value), 'nonfinite JSON number')
        return value

    def invalid(raw):
        raise ValueError('nonfinite JSON constant: ' + raw)

    return json.loads(path.read_text(), object_pairs_hook=pairs,
                      parse_float=number, parse_constant=invalid)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--status', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    status = read_json(args.status)
    need(status['full_threshold_proof_closed'] is False, 'preserve open global scope')
    report = (S / 'reports/RAMANUJAN_SOURCE_FIRST_PV_REPORT.html').read_text()
    replacements = {
        'Gap-data typing is separate from its still-pending numerical GapCheck.':
            'The numerical GapCheck subsequently passed in 305.67 seconds with 38.78 GiB peak '
            'worker RSS and no axioms; it is now closed. Raw-data typing and recurrence '
            'arithmetic remain separate stages.',
        'GapCheck, the other2,767 recurrence chunks and the final count consumer still require '
        'acceptance. A later full-size original chunk is being profiled before an exhaustive '
        'campaign; no full-height count success or mathematical failure is claimed from this '
        'partial frontier.':
            'The exhaustive original arithmetic campaign is active, with exact dated progress '
            'in section14. Its remaining recurrence chunks and final count consumer still '
            'require acceptance. The gap stage and additional bounded proof-decomposition '
            'controls have completed; no full-height count success is claimed from them.',
    }
    for old, new in replacements.items():
        need(report.count(old) == 1, 'exact historical frontier replacement')
        report = report.replace(old, new)
    addendum = (S / 'reports/PACKED_SIEVE_SOURCE_PROVIDER_ADDENDUM.html').read_text()
    need(report.count('</main>') == addendum.count('<main>') == addendum.count('</main>') == 1,
         'exact standalone source reports')
    supplement = addendum.split('<main>', 1)[1].split('</main>', 1)[0]
    supplement = supplement.replace('<h2>', '<h3>').replace('</h2>', '</h3>')
    supplement = supplement.replace(
        '<h1>A different numerical provider for the same verified Ramanujan interval</h1>',
        '<h2>11. Alternative source-linked numerical provider</h2>')
    esc = lambda value: html.escape(str(value))
    grouped = read_json(S / 'evidence/high-grouped-four-pilot-v1/RESULT.json')
    need(grouped['status'] == 'PASS_FOUR_COMPLETE_GROUPED_SAME32768_FACTS_AND_INDEPENDENT_TYPE_AXIOM_AUDIT',
         'complete four-case grouped result required')
    masks = read_json(S / 'evidence/packed-mask-chunking-pilot-v1/SUMMARY.json')
    need(masks['status'] == 'BOUNDED_NEGATIVE_NO_COMPLETE_PRODUCTION_MASK_IDENTITY_ACCEPTED' and
         masks['all_complete_production_identities'] == [], 'retain the bounded negative result')
    combined = read_json(S / 'evidence/prime-base-combined-consumer-v1/RESULT.json')
    need(combined['status'] == 'COMPLETE_SAME_RESULT_COMBINED_PROVIDER_ACTUALLY_CONSUMED_AND_AUDITED'
         and combined['strict_gap'] == 501901 and combined['original_rows'] == 285
         and combined['real_start_inclusive'] == 38358837683
         and combined['real_stop_exclusive'] == 38359837684
         and combined['all_six_existing_C_byte_bindings'] is True
         and combined['old_P_mask_equality_or_baseline_provider_used'] is False
         and combined['old_Lucas_or_ground_local_classifier_provider_used'] is False
         and combined['new_native_C_codec_PV_claim'] is False,
         'require the actual same-result combined-provider acceptance')
    encoding = read_json(S / 'evidence/packed-mask-balanced-data-v1/RESULT.json')
    need(encoding['status'] == 'KERNEL_DATA_ENCODING_AND_STANDALONE_MASK_EQUALITIES_ACCEPTED'
         and encoding['no_new_C_PV'] is True and encoding['no_new_ANT_result'] is True,
         'require the exact kernel-only data-encoding scope')
    codec_replay = read_json(S / 'evidence/packed-mask-balanced-clean-replay-v1/SUMMARY.json')
    need(codec_replay['status'] == 'COMPLETE_CORRECTED_SOURCE_REGENERATION_AND_FRESH_KERNEL_REPLAY'
         and codec_replay['old_application_objects_used'] is False
         and codec_replay['all_normal_O_OO_readbacks_pass'] is True
         and codec_replay['corrected_whole_frontend_terminal_success_marker_observed'] is True
         and codec_replay['runs'][1]['modules'] == 15
         and codec_replay['runs'][1]['compiles'] == 16
         and codec_replay['runs'][1]['failed_compiles'] == 0,
         'require the separate actual corrected codec replay')
    combined_repro = read_json(S / 'evidence/prime-base-combined-clean-v1/RESULT.json')
    need(combined_repro['status'] == 'COMPLETE_ACTUAL_SOURCE_REGEN_ALLMODE_CONTROLS_AND554_BACKEND_PLAN_ONLY'
         and combined_repro['optimization_controls']['actual_routes'] == 41
         and combined_repro['actual_guarded_backend_plan']['modules'] == 554
         and combined_repro['new_full_fresh_combined_Lean_replay_executed'] is False,
         'preserve source-plan versus fresh combined proof distinction')
    appendix = '''<h2>12. Additional completed computational controls</h2>
<article class="card"><h3>Proof decomposition: exact positive controls</h3>
<p>All four tests preserve the same original 32,768 recurrence predicates, original numerical
data and mathematical algorithm. Eight kernel-checked 4,096-entry subfacts and an axiom-free
composition theorem replace a single large reduction. Every complete test and its independent
exact-type audit passed with no axioms. These are kernel proof-evaluation experiments supporting
the count program; they are not new native C program verification or a new prime-count theorem.</p>
<div class="scroll"><table><tr><th>Original part</th><th>Original observed time</th>
<th>Complete grouped proof</th></tr><tr><td>0000</td><td>88.019 s</td><td>75.880 s</td></tr>
<tr><td>0006</td><td>5,501.841 s</td><td>110.513 s</td></tr>
<tr><td>2500</td><td>166.969 s</td><td>143.199 s</td></tr>
<tr><td>0047</td><td>Still running at 8,429.83 s at the comparison cutoff</td><td>229.158 s</td></tr>
</table></div><p>The original 0047 observation is right-censored, not a completed denominator.
The cases were selected to test an observed slow offset, existing early/later controls and an
active outlier; they are not a representative random workload. Shared-host/cache conditions
also limit causal runtime claims. No complete high-count speedup is established.</p>
<p>A separate eight-module test of part 0006 completed in 131.049 seconds including its failed
48 GiB data import and successful unchanged 96 GiB retry. Its eight successful worker CPU times
sum to 125.17 seconds. The grouped four-case study took 619.70 seconds including a controller
disk-scan interruption and recovery. Complete worker peak RSS was at most 4,424,847,360 bytes;
sampled VM and aggregate RSS/PSS values retain their sampling/observation-gap qualifications.</p>
<p>The numerical baseline and all original sources/objects were preserved. Full grouped-count
verification remains a separate proposed extension, not a retroactive success.
<a href="https://github.com/hs-chae/IEANTN_test/tree/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/high-grouped-four-pilot-v1">Exact grouped evidence and reproduction</a>.</p></article>
<article class="card pending"><h3>Partitioning the million-bit mask did not establish a gain</h3>
<p>The bounded scout tried 1, 2, 8 and 16 divisor-fold partitions for the exact same original
million-element mask. The generic composition identity compiled, and nine numerical chunk
equalities passed. No complete proposed partitioned mask identity finished. Eighteen modules
remained unexecuted; censored jobs are not mathematical failures.</p>
<p>Shared setup cost about 49 seconds. Proposed-data compilation alone cost about 48 seconds
for two partitions, 179 seconds for eight and 356 seconds for sixteen. The one-part calibration
and two-part right-half evaluation were censored after exceeding the original 133-second
whole-mask proof cost. Two deadline-censored workers have no final peak-RAM receipts; those
values are unavailable rather than inferred. All scout jobs were drained at the bound.</p>
<p>This result concerns the tested implementation and budget. It neither proves impossibility
nor supports adopting the incomplete variant. The accepted packed provider and its mathematical
conclusions remain unchanged.
<a href="https://github.com/hs-chae/IEANTN_test/tree/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/packed-mask-chunking-pilot-v1">Negative-result evidence and exact reproduction scope</a>.</p></article>'''
    appendix += '''<h2>13. The combined provider is consumed by the real theorem</h2>
<article class="card good"><h3>Closed prime-base certificate, compact data, unchanged C consumer</h3>
<p>The final combined variant preserves all 285 original cell identities, both prime-count
anchors, every Q-prefix computation, all scalar parameters and the same six C source bindings.
It proves the same strict gap greater than 501,901 for every real point from 38,358,837,683
inclusive to 38,359,837,684 exclusive. The complete independent dependency audit passed,
including exact theorem types, the closed new prime-base/data path and exclusion of the old
P-mask equality, old P-data/calibration and local Lucas/classifier proof providers.</p>
<p>The original mask algorithm already uses a small base bitmap to select primes before its
large mask operations. The explicit 17,642-prime list removes conditional iterations through
the same base range. Both implementations restrict the large mask operations to primes.
The list's membership and completeness are proved in the kernel. The balanced 4,096-bit
representation denotes the identical million-bit data; no unverified list or output premise
has been introduced.</p>
<div class="scroll"><table><tr><th>Observed stage</th><th>Seconds</th><th>What was checked</th></tr>
<tr><td>Balanced noncomputable DATA</td><td>4.535</td><td>194,288-byte object; no native code needed for this proof-only definition</td></tr>
<tr><td>Same data, unchanged sieve</td><td>110.734</td><td>Standalone exact original-mask equality</td></tr>
<tr><td>Closed small-prime base</td><td>22.713</td><td>Complete list range/membership and canonical bitmap</td></tr>
<tr><td>Explicit-list mask, precompiled original DATA</td><td>77.762</td><td>Original-fold matched control: 110.482 seconds</td></tr>
<tr><td>Combined list plus compact DATA</td><td>78.534</td><td>Same exact mask; imports neither old P-data nor its equality</td></tr>
<tr><td>All 285 source-count pairs</td><td>27.202</td><td>New P-prefix checks and reused Q proofs through the unchanged C source provider</td></tr>
<tr><td>Real consumer and source-binding wrapper</td><td>4.225 + 4.131</td><td>Same interval, strict margin and byte-bound source programs</td></tr>
<tr><td>Independent full consumer audit</td><td>86.648</td><td>59,328 constants in the gap closure; no numerical or analytic hypothesis</td></tr>
</table></div>
<p>These are separately observed incremental stages with accepted generic/application objects.
Their sum is not a measured end-to-end cold runtime or a statistical speedup. The original
133.066-second mask proof did not include the same data-preparation boundary as every row
above. The compact DATA object is larger than the single-literal 130,928-byte object; the
gain concerns compilation time. The experiments neither establish optimality nor a stronger
number-theoretic conclusion.</p>
<p>A separate fresh replay of the recommended codec now passed all 15 application sources
and the exact-type/axiom audit in 319.199 seconds, using only pinned generic caches.
Maximum worker RSS was 25,910,071,296 bytes; the kernel output occupied 7,897,608 bytes. All 16
compiler invocations returned zero, and normal, optimized and twice-optimized Python
readbacks passed. This replays the unchanged-sieve codec provider; it is not a fresh replay
of the entire combined 285-cell consumer or a pristine-machine provisioning test.</p>
<p>The first fresh mathematical run also passed, but its outer wrapper then gave a file
instead of a directory to a redundant final readback. That failure is preserved. The
corrected whole frontend reached its terminal success marker with empty stderr; its
detached outer OS exit code was not captured. Child exit records and every final readback
are retained. No system-wide kernel OOM counter baseline was recorded for these small
replays; none of their compiler workers was killed or reported OOM.</p>
<p>The new combined-consumer recipe also regenerated its complete 554-source population
from published inputs and passed 41 actual Python-mode and rejection controls. The unchanged
proof backend independently confirmed every planned source hash and import edge. Default
source preparation took 150.515 seconds; optimized-mode controls explicitly reused the
original regenerated source tree while regenerating the new provider inputs. No application
proof objects were reused for planning, and no new full 554-source proof replay was executed.
The combined mathematical theorem has the separate accepted incremental builds above.
<a href="https://github.com/hs-chae/IEANTN_test/blob/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/REPRODUCE_PRIME_BASE_COMBINED_CLEAN.md">Exact clean-clone bootstrap and executable recipe</a>.</p>
<p>The list fold and data codec are kernel numerical providers, not source-first PV of a new
native bitset program. The source-first result continues to use the actual verified C counter,
segmented checker, exponential, logarithm and cell executions. Physical input loading, native
callers and process/output association remain outside those function-level proofs. The
selected mathematical closures contain only Lean's standard logical axioms and no
<code>native_decide</code> execution axioms.</p>
<p><a href="https://github.com/hs-chae/IEANTN_test/blob/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/RamanujanPV/PrimeBaseCombinedResult.lean">Exact combined source-bound theorem</a> ·
<a href="https://github.com/hs-chae/IEANTN_test/blob/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/RamanujanPV/PrimeBaseCombinedIndependentAudit.lean">Required/forbidden dependency and exact-type audit</a> ·
<a href="https://github.com/hs-chae/IEANTN_test/tree/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/prime-base-combined-consumer-v1">Consumer receipts and reproduction boundary</a> ·
<a href="https://github.com/hs-chae/IEANTN_test/tree/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/packed-mask-balanced-data-v1">Original sealed encoding evidence</a> ·
<a href="https://github.com/hs-chae/IEANTN_test/tree/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/packed-mask-balanced-clean-replay-v1">Corrected executable recipe and actual fresh-replay evidence</a>.</p></article>'''
    rows = ''.join('<tr><td>' + esc(row['study']) + '</td><td>' + esc(row['observed']) +
                   '</td><td>' + esc(row['acceptance']) + '</td></tr>' for row in status['runs'])
    appendix += ('<h2>14. Dated checkpoint and remaining work</h2><article class="card pending">'
                 '<h3>The requested global threshold is not proved</h3><p>Observed at ' +
                 esc(status['observed_utc']) + '. These are dated process/receipt observations, '
                 'not live status after download.</p><div class="scroll"><table><tr><th>Study</th>'
                 '<th>Observed progress</th><th>Acceptance boundary</th></tr>' + rows +
                 '</table></div><p>The remaining central obligation is the actual source-linked '
                 'prime-count evidence across the entire missing finite prefix. Closed scalar '
                 'executions, a million-unit local theorem, a single high endpoint or an active '
                 'controller cannot replace that evidence. The analytic ray and its exact 25 '
                 'external inputs retain their separate completed mathematical scope.</p>'
                 '<p>The active 1.49-trillion count is the original fixed scalability benchmark. '
                 'The new 1.25-trillion analytic ray permits a shorter finite prefix; completing '
                 'that one benchmark does not finish the required prime-count coverage.</p>'
                 '<p><a href="https://github.com/hs-chae/IEANTN_test/blob/research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/evidence/RAMANUJAN_RESEARCH_CHECKPOINT_INVENTORY.json">'
                 'Machine-readable checkpoint inventory: eight selected final declarations and six C sources'
                 '</a>. This is an explicitly selected research inventory, not an exhaustive IEANTN '
                 'source-claim census.</p></article>')
    report = report.replace('</main>', supplement + appendix + '</main>')
    report = report.replace('</style>',
        '.scroll-hint{display:none}.scroll:focus-visible{outline:2px solid #135c9a;outline-offset:3px}'
        '@media(max-width:600px){table{min-width:620px}th,td{white-space:normal;max-width:300px}'
        'th:first-child,td:first-child{width:160px;max-width:160px}'
        '.scroll-hint{display:block;font-size:13px;color:#536579;margin:4px 0 10px}}'
        '</style>', 1)
    report = report.replace('<div class="scroll">',
        '<div class="scroll" tabindex="0" aria-label="Table: scroll sideways for remaining columns">'
        '<p class="scroll-hint">Scroll sideways to view all columns.</p>')
    report = report.replace('Research checkpoint, 2026-11-20 07:45 UTC.',
                            'Consolidated research checkpoint, ' + esc(status['observed_utc']) +
                            '. Earlier measurements retain their stated dates and scopes.', 1)
    report = report.replace('<title>Ramanujan', '<title>Full research checkpoint: Ramanujan', 1)
    raw = report.encode()
    need(raw.count(b'<math') == 70, 'all 63 original and 7 companion expressions retained')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(raw)
    args.out.with_suffix('.sha256').write_text(hashlib.sha256(raw).hexdigest() + '\n')
    print(json.dumps({'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                      'math_nodes': raw.count(b'<math')}))


if __name__ == '__main__':
    main()
