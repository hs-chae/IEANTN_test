#!/usr/bin/env python3
"""Actual normal/-O/-OO fresh-gate and format-export controls on S13."""
import argparse, json, shutil, subprocess, sys
from pathlib import Path
from reproduce_dual import load, need, publish, sha
from test_fft_dag_nested_verifier import clone

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['run', 'context', 'candidate', 'out']:
        ap.add_argument('--' + name, type=Path, required=True)
    a = ap.parse_args(); need(not a.out.exists(), 'Fresh control directory required')
    need(load(a.run / 'RESULT.json')['stages'] == 13, 'Bounded S13 fixture only')
    a.out.mkdir(); records = []
    for mode in range(3):
        flags = ['-' + 'O' * mode] if mode else []
        for case in ['positive', 'axiom-audit', 'compiler-flags', 'RSS-summary',
                     'missing-result', 'wrong-numerical-target']:
            fixture = None; run = a.run
            if case != 'positive':
                fixture = a.out / (case + '-' + str(mode)); clone(a.run, fixture); run = fixture
                if case == 'missing-result':
                    (run / 'RESULT.json').unlink()
                elif case == 'axiom-audit':
                    p = run / 'AXIOM_AUDIT.json'; v = load(p)
                    v['roots'][0]['axioms'].append('UnverifiedAxiom'); p.write_text(json.dumps(v))
                elif case == 'compiler-flags':
                    p = run / 'W4D13ClaimAudit.COMPILED.json'; v = load(p)
                    v['command'].append('--trust=1'); p.write_text(json.dumps(v))
                else:
                    p = run / 'RESULT.json'; v = load(p)
                    v['max_individual_RSS_KiB' if case == 'RSS-summary' else 'norm_numerator'] += 1
                    p.write_text(json.dumps(v))
            receipt = a.out / (case + '-accepted-' + str(mode) + '.json')
            command = [sys.executable, *flags, str(HERE / 'verify_fft_dag_fresh_v3.py'),
                       '--run', str(run), '--context', str(a.context), '--candidate',
                       str(a.candidate), '--proof-only-toy', '--output', str(receipt)]
            p = subprocess.run(command, capture_output=True, text=True)
            (a.out / (case + '-' + str(mode) + '.stderr')).write_text(p.stderr)
            need(p.returncode == 0 and receipt.is_file() if case == 'positive'
                 else p.returncode != 0 and not receipt.exists(), 'Fresh CLI wrong result: ' + case)
            records.append(dict(case=case, mode=mode, command=command, returncode=p.returncode))
            if fixture:
                need(fixture.parent == a.out and not fixture.is_symlink(), 'Owned fixture only')
                shutil.rmtree(fixture)
        accepted = a.out / ('positive-accepted-' + str(mode) + '.json')
        bank = a.out / ('export-' + str(mode))
        command = [sys.executable, *flags, str(HERE / 'export_fft_dag_fresh_bank_v3.py'),
                   '--base', str(a.run), '--context', str(a.context), '--candidate',
                   str(a.candidate), '--accepted', str(accepted), '--run', str(bank), '--toy']
        p = subprocess.run(command, capture_output=True, text=True)
        need(p.returncode == 0 and (bank / 'RESULT.json').is_file(), 'Fresh format adapter failed')
        records.append(dict(case='fresh-format-export', mode=mode, command=command,
                            returncode=p.returncode))
    publish(a.out / 'RESULT.json', dict(
        status='PASS_ACTUAL_FRESH_GATE3_POSITIVE15_REJECTION_AND3_FORMAT_EXPORT_ALL_MODES',
        mathematical_fixture_unchanged=True, original_payloads_unchanged=True,
        production_N24_resource_gate_not_exercised=True, records=records,
        gate_sha256=sha(HERE / 'verify_fft_dag_fresh_v3.py'),
        adapter_sha256=sha(HERE / 'export_fft_dag_fresh_bank_v3.py'),
        harness_sha256=sha(Path(__file__))))
    print('PASS original fresh S13 gate3/15 and3 format exports in normal/O/OO')


if __name__ == '__main__':
    main()
