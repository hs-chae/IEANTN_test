#!/usr/bin/env python3
"""Bounded actual v4 CLIs: three historical phases and new AS_UNLIMITED compilation.

The complete S13 fixture supplies 118 original +1 v1 +1 v2 proofs. A second
partial v2 fixture leaves only the cheap typed audit to compile under AS_UNLIMITED.
The expensive Final proof is never rerun by these controls.
"""
import argparse, json, os, shutil, subprocess, sys
from pathlib import Path
from reproduce_dual import load, need, publish, sha
from test_fft_dag_nested_verifier import clone

HERE = Path(__file__).resolve().parent


def invoke(command, out, tag):
    with (out / (tag + '.stdout')).open('xb') as f, (out / (tag + '.stderr')).open('xb') as g:
        result = subprocess.run(command, stdout=f, stderr=g)
    return result.returncode


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context', 'candidate', 'completed-v2', 'out']:
        ap.add_argument('--' + name, required=True, type=Path)
    a = ap.parse_args(); need(not a.out.exists(), 'Fresh bounded controls required')
    p = load(a.completed_v2 / 'PLAN.json'); r = load(a.completed_v2 / 'RESULT.json')
    need(r['stages'] == 13 and p['successful_prefix_modules'] == 119
         and r['freshly_compiled_modules'] == 1, 'Exact bounded v2 fixture required')
    a.out.mkdir(); partial = a.out / 'v2-before-audit-fixture'; clone(a.completed_v2, partial)
    for n in ['W4D13ClaimAudit.COMPILED.json', 'RESULT.json', 'AXIOM_AUDIT.json']:
        (partial / n).unlink()
    # Leave the unreceipted object: v4 must compile it anew, never silently reuse.
    records = []; prefix = p['original_prefix']; prior = p['continuation_plans'][0]['path']
    for mode in range(3):
        flags = ['-' + 'O' * mode] if mode else []
        for tag, parent in [('three-phases', a.completed_v2), ('fresh-AS-unlimited', partial)]:
            run = a.out / (tag + '-' + str(mode))
            command = [sys.executable, *flags, str(HERE / 'resume_fft_dag_source_cold_v4.py'),
                       '--context', str(a.context), '--candidate', str(a.candidate),
                       '--prefix', prefix, '--continuation', prior,
                       '--nested-continuation', str(parent), '--run', str(run),
                       '--workers', '1', '--worker-virtual-as', 'unlimited']
            code = invoke(command, a.out, tag + '-' + str(mode))
            need(code == 0 and (run / 'RESULT.json').is_file(), 'Actual v4 CLI failed')
            result = load(run / 'RESULT.json')
            need(result['freshly_compiled_modules'] == (0 if tag == 'three-phases' else 1),
                 'Fresh AS_UNLIMITED audit was not actually compiled')
            if tag == 'fresh-AS-unlimited':
                receipt = load(run / 'W4D13ClaimAudit.COMPILED.json')
                need('--as=unlimited' in receipt['resource_command'],
                     'Actual compiler did not receive initial AS_UNLIMITED')
            accepted = a.out / (tag + '-accepted-' + str(mode) + '.json')
            gate = [sys.executable, *flags, str(HERE / 'verify_fft_dag_nested_resume_v4.py'),
                    '--context', str(a.context), '--candidate', str(a.candidate),
                    '--run', str(run), '--proof-only-toy', '--output', str(accepted)]
            need(invoke(gate, a.out, tag + '-gate-' + str(mode)) == 0 and accepted.is_file(),
                 'Actual v4 independent gate failed')
            records.append(dict(case=tag, mode=mode, command=command, returncode=code,
                                result_sha256=sha(run / 'RESULT.json')))
            if tag == 'fresh-AS-unlimited':
                bank = a.out / ('export-' + str(mode))
                command = [sys.executable, *flags, str(HERE / 'export_fft_dag_bank_v4.py'),
                           '--base', str(run), '--context', str(a.context), '--candidate',
                           str(a.candidate), '--accepted', str(accepted), '--run', str(bank), '--toy']
                need(invoke(command, a.out, 'export-' + str(mode)) == 0,
                     'Actual v4 format export failed')
        for case in ['controller', 'helper', 'route', 'AS-command', 'compiler-flags',
                     'PANIC-exit0', 'missing-dependency', 'phase-count']:
            fixture = a.out / (case + '-' + str(mode) + '-fixture'); clone(a.completed_v2, fixture)
            if case in ['controller', 'helper', 'route', 'AS-command', 'phase-count']:
                q = fixture / 'PLAN.json'; v = load(q)
                if case == 'controller': v['controller_sha256'] = '0' * 64
                elif case == 'helper': v['continuation_helper_sha256'] = '0' * 64
                elif case == 'route': v['routes'][next(iter(v['routes']))]['compile_origin'] += '-wrong'
                elif case == 'AS-command': v['per_compiler_AS_bytes'] += 1
                else: v['successful_prefix_modules'] += 1
                q.write_text(json.dumps(v))
            elif case == 'missing-dependency':
                (fixture / 'W4D13Final.COMPILED.json').unlink()
            else:
                q = fixture / 'W4D13ClaimAudit.COMPILED.json'; v = load(q)
                if case == 'compiler-flags': v['command'].append('--trust=1')
                else:
                    log = fixture / 'W4D13ClaimAudit.stdout'; log.unlink(); log.write_text('PANIC exit0\n')
                    v['stdout_sha256'] = sha(log)
                q.write_text(json.dumps(v))
            bad = a.out / ('must-reject-' + case + '-' + str(mode))
            command = [sys.executable, *flags, str(HERE / 'resume_fft_dag_source_cold_v4.py'),
                       '--context', str(a.context), '--candidate', str(a.candidate),
                       '--prefix', prefix, '--continuation', prior, '--nested-continuation',
                       str(fixture), '--run', str(bad), '--workers', '1',
                       '--worker-virtual-as', 'unlimited', '--prepare-only']
            code = invoke(command, a.out, case + '-negative-' + str(mode))
            need(code != 0 and not (bad / 'RESULT.json').exists(), 'V3 accepted tampered phase')
            records.append(dict(case=case, mode=mode, command=command, returncode=code))
            need(fixture.parent == a.out and not fixture.is_symlink(), 'Owned fixture cleanup only')
            shutil.rmtree(fixture)
    publish(a.out / 'RESULT.json', dict(
        status='PASS_V4_ACTUAL_THREE_PHASE_AND_FRESH_AS_UNLIMITED_NORMAL_O_OO_24_REJECTIONS',
        three_phase_positive=3, fresh_AS_UNLIMITED_compilation_positive=3, rejections=24,
        format_export_positive=3, original_sources_and_outcomes_unchanged=True,
        large_final_module_not_recompiled=True, production_NOT_launched=True,
        records=records, controller_sha256=sha(HERE / 'resume_fft_dag_source_cold_v4.py'),
        helper_sha256=sha(HERE / 'fft_dag_nested_lineage_v3.py'),
        gate_sha256=sha(HERE / 'verify_fft_dag_nested_resume_v4.py'),
        exporter_sha256=sha(HERE / 'export_fft_dag_bank_v4.py')))
    print('PASS v4: 3 historical phases, actual AS_UNLIMITED audit compilation,24 rejections')


if __name__ == '__main__':
    main()
