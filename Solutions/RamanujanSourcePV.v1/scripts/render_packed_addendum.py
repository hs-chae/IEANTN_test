#!/usr/bin/env python3
"""Render a standalone, static-math account of the accepted packed provider."""
from pathlib import Path
import argparse
import base64
import hashlib
import html
import json
import sys

S = Path(__file__).resolve().parents[1]


def need(value, message):
    if not value:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--python-packages', type=Path, required=True)
    parser.add_argument('--review', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    review = json.loads(args.review.read_text())
    need(review['status'] == 'REVIEWED_CURRENT_PACKED_MILLION_SOURCE_AND_MATHEMATICAL_CHAIN',
         'independent final audit and current-byte review required')
    need(review['global_target_closed'] is False, 'preserve the open full target')
    result = json.loads((S / 'evidence/PACKED_SIEVE_SCALABILITY_RESULT.json').read_text())
    math = result['mathematical_result']
    need((math['lower_included'], math['upper_excluded'],
          math['uniform_gap_strictly_greater_than']) == (38358837683, 38359837684, 501901),
         'exact original mathematical statement')
    sys.path.insert(0, str(args.python_packages))
    from latex2mathml.converter import convert
    esc = lambda text: html.escape(str(text))
    font = base64.b64encode((S / 'reports/fonts/STIXGeneral.ttf').read_bytes()).decode()
    root = ('https://github.com/hs-chae/IEANTN_test/blob/'
            'research/ramanujan-source-first-pv-20261119/Solutions/RamanujanSourcePV.v1/')

    def link(path, label):
        return '<a href="' + root + path + '">' + esc(label) + '</a>'

    def eq(source):
        return '<div class="eq">' + convert(source, display='block') + '</div>'

    def card(title, body, kind='good'):
        return '<section class="card ' + kind + '"><h2>' + title + '</h2>' + body + '</section>'

    body = ['<!doctype html><html lang="en"><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>Ramanujan: packed source-provider result</title><style>'
            '@font-face{font-family:STIX;src:url(data:font/ttf;base64,' + font + ') format("truetype")}'
            '*{box-sizing:border-box}body{margin:0;padding:16px;background:#edf3f7;color:#193047;'
            'font:16px/1.6 system-ui,sans-serif;overflow-wrap:anywhere}main{max-width:1000px;margin:auto;'
            'padding:24px;background:white;border-radius:12px}h1{line-height:1.2;font-size:29px}'
            'h2{font-size:21px;margin:0 0 10px}.card{margin:18px 0;padding:18px;border-left:6px solid #287657;'
            'background:#f2f9f5;border-radius:6px}.pending{border-color:#b47818;background:#fff7e8}'
            '.ordinary{border-color:#78659b;background:#f5f1fa}.eq,.scroll{overflow:auto;max-width:100%}'
            '.eq{padding:12px;background:#eaf1f8;margin:14px 0}math{font:21px STIX,serif}'
            'a{color:#135c9a}table{border-collapse:collapse;min-width:660px;width:100%;font-size:14px}'
            'td,th{text-align:left;padding:9px;border-bottom:1px solid #ccd8e1;vertical-align:top}'
            'code{font-size:13px}small{color:#536579}@media(max-width:500px){body{padding:7px}'
            'main{padding:14px}.card{padding:13px}h1{font-size:25px}math{font-size:18px}}</style><main>',
            '<h1>A different numerical provider for the same verified Ramanujan interval</h1>']
    body.append(card('Completed local theorem; full target remains open',
        '<p>The alternative packed-bit route proves the original million-unit result about the actual '
        'IEANTN prime-counting function. It preserves all 285 recorded cell parameters, the mathematical '
        'statement, the two source-verified anchor counts, and the existing C exponential, logarithm '
        'and strict-cell programs. This finite theorem is unconditional.</p>' +
        eq(r'G(x)=\frac{ex}{\log x}\pi(x/e)-\pi(x)^2,\qquad G(x)>501901\quad'
           r'(38358837683\le x<38359837684).') +
        '<p>' + link('RamanujanPV/PackedSieveMillion.lean', 'Actual final Lean declarations') +
        ': <code>complete_certificate</code>, <code>first_1000001_real_interval</code> and '
        '<code>uniform_gap</code>. ' + link('RamanujanPV/PackedSieveResult.lean', 'The joint source-linked result') +
        ' additionally packages all six byte/AST bindings with the same real conclusion. '
        'The full theorem from the requested lower threshold remains open '
        'because the intervening finite prime-count evidence is missing.</p>', 'pending'))
    body.append(card('What changed, and which part is source-first PV',
        '<p>The previous local provider used 116,176 recursive primality proofs, including auxiliary '
        'primes. The new provider proves two entire integer bitmasks and counts disjoint slices to '
        'recover every original prime-count pair. The final proof does not use those old primality '
        'providers. Incidental old raw data remain imported to preserve the original cell definitions; '
        'an unused data import is distinguished from a mathematical proof dependency.</p>'
        '<p>The mask and population-count arithmetic is <strong>kernel-only numerical verification</strong>. '
        'There is no new verified native packed C implementation. The <strong>source-first PV</strong> '
        'chain uses the unchanged executable C segmented checker: exact source/AST correspondence, '
        'typed operational semantics, proved owned inputs and initialization, complete C execution, '
        'positive-output soundness, source count objects, and the real mathematical consumer.</p>' +
        '<p>' + link('c/verified_segment_checker.c', 'Actual 837-byte C source') +
        ' · ' + link('RamanujanPV/PackedSieveProvider.lean', 'Source-bound provider') +
        ' · ' + link('RamanujanPV/PackedSieveQueries.lean', 'All 285 source-count pairs') + '</p>'
        '<p><code>SHA-256: 7689437a39f22d151b0d793b7a91fe766f26d91de89b5894a3e67afdd54a6959</code></p>'))
    body.append(card('Why every bit represents primality',
        '<p>Take an integer window starting at ℓ ≥ 2 with length m &gt; 0. Each divisor mask marks exactly its '
        'multiples at or above its square. Taking their bitwise union marks every composite and no prime. '
        'The actual Lean <code>PackedSieveKernel.compositeMask</code> first builds a smaller '
        'composite bitmap and uses it to skip composite divisors. The displayed union over all '
        'divisors is an equivalent mathematical characterization, not a claim that the Lean '
        'implementation evaluates every large divisor mask. The C checker itself visits all '
        'divisors in its source loop. The generic proof uses least prime divisors and assumes no '
        'unverified prime list or supplied classification. '
        'For the source instances, the upper integer is at most 2 trillion and the length fits the '
        'fixed 1,500,000-word storage.</p>' +
        eq(r'M_d=\sum_{\substack{0\le i<m\\d^2\le\ell+i\\d\mid\ell+i}}2^i,'
           r'\qquad C=\bigvee_{2\le d\le\lfloor\sqrt{\ell+m-1}\rfloor}M_d,\qquad Z=2^m-1.') +
        eq(r'P=Z\mathbin{\&}\neg C=Z\mathbin{\oplus}(Z\mathbin{\&}C),\qquad'
           r'\operatorname{bit}_i(P)=1\ \Longleftrightarrow\ \ell+i\text{ is prime}\quad(0\le i<m).') +
        '<p>The complement is within the m-bit window. The AND/XOR rewrite is proved for every input. '
        'The numerical kernel checks then identify '
        'every bit of the proposed P and Q masks, rather than trusting their expected counts.</p>' +
        eq(r'(\ell_P,m_P)=(38358837684,1000000),\qquad'
           r'(\ell_Q,m_Q)=(14111427771,367880).') +
        '<p>' + link('RamanujanPV/PackedSieveGeometric.lean', 'Exact geometric masks') +
        ' · ' + link('RamanujanPV/PackedSieveCorrect.lean', 'Full primality classification') +
        ' · ' + link('RamanujanPV/PackedSievePrimitiveBits.lean', 'Exact primitive rewrite') + '</p>'))
    body.append(card('Disjoint slices retain every required count',
        '<p>A proved 256-entry byte table gives exact population counts, including partial-byte padding. '
        'Instead of separately scanning every full prefix, the checker counts disjoint sorted slices '
        'and accumulates them. All 285 original P/Q identities are kernel-checked. The source provider '
        'then supplies the actual C checker with represented claim words and consumes its completed '
        'execution to obtain the source count at each requested index.</p>' +
        eq(r'\pi(\ell+i)=\pi(\ell-1)+'
           r'\operatorname{popcount}\bigl(P\bmod2^{i+1}\bigr)\qquad(0\le i<m).') +
        '<p>Both anchor counts are the previously accepted exact values, now imported through a small '
        'source adapter. No expected output, correct-flag oracle or desired Ramanujan positivity is an '
        'extra hypothesis.</p>' + link('RamanujanPV/PackedSieveSlices.lean', 'Slice correctness') +
        ' · ' + link('RamanujanPV/PackedSieveAnchors.lean', 'Unchanged source-verified anchors') +
        '<p>The same slice identities also prove the original whole-byte-count expression equals '
        '40,916, without evaluating its slow monolithic reduction again. The independently compiled '
        'source-count endpoint adapters yield:</p>' +
        eq(r'\pi(38359837683)=1644714148,\qquad\pi(14111795650)=632223009.') +
        '<p>' + link('RamanujanPV/PackedSieveCounts.lean', 'Recovered whole count and source-linked P endpoint') +
        ' · ' + link('RamanujanPV/PackedSieveQSource.lean', 'Source-linked Q endpoint') + '</p>'))
    stage_labels = {
        'P_mask': 'Every bit of the million-element P mask',
        'Q_mask_and_count': 'Every Q mask bit and its complete count',
        'Q_285_prefixes': 'All 285 Q prefixes',
        'P_Q_285_prefixes_source_counts': 'All 285 count pairs and C source counts',
        'final_real_consumer': 'Final real-interval theorem',
    }
    stage_rows = []
    for row in result['stages']:
        stage_rows.append('<tr><td>' + esc(stage_labels.get(row['stage'], row['stage'])) + '</td><td>' +
            f"{row['elapsed_seconds']:.3f} s" + '</td><td>' +
            f"{row['peak_worker_rss_bytes'] / 2**30:.2f} GiB" + '</td></tr>')
    body.append(card('Measured successful stages',
        '<div class="scroll"><table><tr><th>Actual accepted stage</th><th>Wall time</th>'
        '<th>Process peak RSS</th></tr>' + ''.join(stage_rows) + '</table></div>'
        '<p>These are actual per-process GNU-time measurements on a shared host. Their sum is not an '
        'end-to-end clean-build benchmark. The two large anchor proofs are reused by both methods; '
        'their cost is not removed. The old local-primality proof dependency is removed, but no global '
        'runtime or memory advantage is established by comparing unlike scopes.</p>'
        '<p>The generic provider separately passed a fresh 56-source build plus final audit in 378.742 '
        'seconds, with 30.07 GiB maximum worker RSS, no old application objects and zero OOM events. '
        'That replay is not a fresh rebuild of the entire new million theorem. ' +
        esc(review['new_full_cold_replay_status']) + '</p>'))
    body.append(card('Native observations and unsuccessful attempts remain separate',
        '<p>The exact unchanged C checker was compiled and run on both accepted masks. Returns were '
        '40,917 and 15,973, which encode count plus one. Mutated claims and insufficient capacity '
        'returned zero. Actual normal, -O and -OO observer routes passed. The caller and physical '
        'input loading are unverified: these observations support reproducibility and do not supply '
        'the Lean numerical proof.</p><p>The retained unsuccessful or censored profiles are:</p><ul>' +
        '<li>The initial 48 GiB SWAR attempt failed with a GMP allocation error after 178.52 seconds '
        '(exit 134). No OS OOM event was established.</li>'
        '<li>The 192 GiB SWAR timing attempt was intentionally cancelled after 961.11 seconds.</li>'
        '<li>The original bit-difference Q/whole-byte route was intentionally cancelled after '
        '1,076.71 seconds; the P seal attempt was cancelled after 141.10 seconds.</li>'
        '<li>The primitive P whole-population-count attempt ended with SIGTERM (exit 143), without '
        'a completed receipt. Its cause is unknown.</li>'
        '<li>A detached retry of that whole-count attempt was intentionally stopped after the exact '
        'P mask passed and the slice method became available.</li>' +
        '</ul><p>An unexplained SIGTERM is not reported as OOM or a mathematical failure. Completion '
        'times of interrupted whole-mask population counts are unknown; no speedup ratio is inferred.</p>', 'ordinary'))
    body.append(card('Audited scope, remaining trust and reproduction',
        '<p>' + esc(review['independent_audit_summary']) + '</p>'
        '<p>The audit concerns the listed new final theorems, not every declaration in IEANTN. Only '
        'the three standard logical axioms occur; no sorry, native execution axiom or unproved SWAR '
        'count is used. The Lean kernel and its pinned executable, core arithmetic implementation '
        'and hardware remain trusted. Native observations additionally use the pinned C compiler, '
        'runtime, ABI and OS; those observations are kept outside the mathematical acceptance chain. '
        'A physical claim loader, caller and process/stdout association are not proved by these '
        'function contracts.</p><p>There is no new official Blueprint node. This is a solution-local '
        'replacement provider for the same certificate, corresponding to the imported '
        '<a href="https://github.com/hs-chae/IEANTN_test/blob/research/ramanujan-source-first-pv-20261119/'
        'IEANTN/Nodes/DudekPlatt/v3/Conclusions.lean">DudekPlatt.v3 network module</a>. '
        'No original network outcome or theorem premise is silently replaced.</p><p>' +
        link('PACKED_SIEVE_REPRODUCTION.md', 'Exact numerical regeneration and build instructions') +
        ' · ' + link('REPRODUCE_PACKED_SIEVE.md', 'Fresh generic provider reproduction') +
        ' · ' + link('evidence/PACKED_SIEVE_SCALABILITY_RESULT.json', 'Source hashes, commands and measured receipts') +
        '</p><p>The separate analytic improvement is already proved under its exact 25 explicit '
        'inputs; it is not a consequence of this packed numerical experiment.</p>' +
        eq(r'G(x)>6\cdot10^{12}\qquad(x\ge1.25\cdot10^{12}).') +
        '<p>The still-missing finite range between the local window and this analytic onset prevents '
        'a completed proof of the full requested threshold. The active 1.49-trillion endpoint study '
        'verifies one count, not every count needed across that range.</p>', 'pending'))
    body.append('<small>Static MathML with embedded licensed STIX font. No CDN, script, browser extension '
                'or external renderer is required. Original results and failed attempts are preserved.</small></main></html>')
    rendered = '\n'.join(body).encode()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(rendered)
    args.out.with_suffix('.sha256').write_text(hashlib.sha256(rendered).hexdigest() + '\n')
    print(json.dumps({'bytes': len(rendered), 'sha256': hashlib.sha256(rendered).hexdigest(),
                      'math_nodes': rendered.count(b'<math')}))


if __name__ == '__main__':
    main()
