#!/usr/bin/env python3
"""Actual all-mode generation/readback and rejection controls; no Lean proofs."""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
from reproduce_guarded_coupled_closure import strict_json, need, sha

S = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--normal-prepared', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--cpus', default='10,11')
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh control output')
    out.mkdir()
    frontend = S / 'scripts/reproduce_prime_base_combined.py'
    identity = sha(frontend)
    records = []

    def route(mode, name, arguments, accept):
        command = [sys.executable, *mode, str(frontend), *map(str, arguments)]
        stdout, stderr = out / (name + '.stdout'), out / (name + '.stderr')
        with stdout.open('w') as so, stderr.open('w') as se:
            code = subprocess.call(command, stdout=so, stderr=se)
        need((code == 0) is accept, 'actual expected CLI outcome ' + name)
        need(sha(frontend) == identity, 'frontend stayed frozen')
        records.append({'name': name, 'command': command, 'exit_code': code, 'expected_accept': accept,
                        'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)})

    for label, mode in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        prepared = args.normal_prepared.resolve() if not mode else out / ('generated-' + label)
        if mode:
            baseline = strict_json(args.normal_prepared / 'PREPARED.json')
            original_source = (Path(baseline['prepared_root']) if baseline['source_preparation_reused'] else
                               args.normal_prepared / 'original-sources/prepared-baseline')
            route(mode, 'generate-' + label, ['--context', args.context, '--out', prepared,
                  '--plan-only', '--prepared-root', original_source,
                  '--jobs', 1, '--cpus', args.cpus], True)
        route(mode, 'positive-plan-' + label, ['--check-plan', prepared], True)
        route(mode, 'plan-is-not-proof-' + label, ['--check', prepared], False)
        route(mode, 'mixed-modes-' + label, ['--check-plan', prepared, '--out', out / 'unused'], False)
        original = strict_json(prepared / 'PREPARED.json')
        plan = strict_json(prepared / 'COMBINED_PLAN.json')
        original_bytes = (prepared / 'PREPARED.json').read_bytes()
        plan_bytes = (prepared / 'COMBINED_PLAN.json').read_bytes()
        (out / ('original-receipt-' + label + '.json')).write_bytes(original_bytes)
        (out / ('original-plan-' + label + '.json')).write_bytes(plan_bytes)
        # These are experiment-owned source-only control receipts, with no
        # worker or mathematical acceptance depending on them. Save exact
        # originals and restore them even if a deliberate rejection fails.
        def write(value, plan_value=plan):
            (prepared / 'PREPARED.json').write_text(json.dumps(value, indent=2) + '\n')
            (prepared / 'COMBINED_PLAN.json').write_text(json.dumps(plan_value, indent=2) + '\n')
        try:
            for case in ['population', 'lock', 'frontend', 'theorem', 'empty-pins', 'empty-commands', 'backend-command']:
                value = json.loads(json.dumps(original))
                changed_plan = json.loads(json.dumps(plan))
                if case == 'population': value['sources'] = value['sources'][:-1]
                elif case == 'lock': value['source_lock_sha256'] = '0' * 64
                elif case == 'frontend': value['frontend_sha256'] = '0' * 64
                elif case == 'empty-pins': value['script_pins'] = {}
                elif case == 'empty-commands': value['commands'] = []
                elif case == 'backend-command': changed_plan['backend_command'] = ['python3', 'unrelated.py']
                else: changed_plan['theorems'] = ['Nat.add_comm']
                write(value, changed_plan)
                route(mode, case + '-rejected-' + label, ['--check-plan', prepared], False)
            write(original)
            text = (prepared / 'PREPARED.json').read_text()
            (prepared / 'PREPARED.json').write_text(text[:-2] + ',"invalid":1e999}\n')
            route(mode, 'nonfinite-rejected-' + label, ['--check-plan', prepared], False)
            (prepared / 'PREPARED.json').write_text(text[:-2] + ',"status":"duplicate"}\n')
            route(mode, 'duplicate-rejected-' + label, ['--check-plan', prepared], False)
        finally:
            (prepared / 'PREPARED.json').write_bytes(original_bytes)
            (prepared / 'COMBINED_PLAN.json').write_bytes(plan_bytes)
        route(mode, 'restored-positive-' + label, ['--check-plan', prepared], True)
    result = {'status': 'PASS_ACTUAL_ALL_MODE_SOURCE_GENERATION_PLAN_READBACK_AND_REJECTIONS',
              'frontend_sha256': identity, 'test_script_sha256': sha(Path(__file__)),
              'source_lock_sha256': sha(S / 'evidence/prime-base-combined-clean-v1/SOURCE_LOCK.json'),
              'routes': records, 'normal_generation': str(args.normal_prepared.resolve()),
              'normal_generation_separate_actual_execution': True,
              'full_fresh_combined_proof_execution_run': False,
              'scope': 'Actual normal default source generation; O/OO regenerate combined support and stage/hash-check exact original source reused from that run. No proof objects or new Lean proof run.'}
    (out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'routes': len(records)}))


if __name__ == '__main__':
    main()
