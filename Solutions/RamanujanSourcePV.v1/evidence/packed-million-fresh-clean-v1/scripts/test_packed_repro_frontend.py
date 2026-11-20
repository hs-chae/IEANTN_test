#!/usr/bin/env python3
"""Actual all-mode source staging and completed-scope rejection controls."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from reproduce_guarded_coupled_closure import strict_json, need, sha

S = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--prepared-root', type=Path, required=True)
    parser.add_argument('--unrelated-completed-backend', type=Path, required=True)
    parser.add_argument('--cpus', default='10,11')
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh owned control directory')
    out.mkdir()
    front = S / 'scripts/reproduce_packed_million.py'
    helper = S / 'scripts/reproduce_guarded_coupled_closure.py'
    lock_path = S / 'evidence/packed-numerical-source-v1/BOUND_SOURCE_LOCK.json'
    lock = strict_json(lock_path)
    unrelated = args.unrelated_completed_backend.resolve()
    need(strict_json(unrelated / 'RESULT.json')['status'] == 'FRESH_SELECTED_SOURCE_CLOSURE_PASS',
         'real unrelated completed proof backend')
    shutil.copyfile(front, out / 'frontend.py')
    rows = []

    def execute(mode, flags, case, command, accept, reason=None):
        run = subprocess.run([sys.executable, *flags, *map(str, command)], capture_output=True,
            text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
        record = {'mode': mode, 'case': case, 'command': [sys.executable, *flags, *map(str, command)],
                  'exit_code': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
        rows.append(record)
        (out / 'PROGRESS.json').write_text(json.dumps(rows, indent=2) + '\n')
        need((run.returncode == 0) == accept and (reason is None or reason in run.stderr),
             'actual expected CLI verdict: ' + mode + '/' + case)
        print(mode, case, run.returncode, flush=True)

    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        execute(mode, flags, 'bound549-source-only', [front, '--out', out / (mode + '-staging'),
            '--prepared-root', args.prepared_root.resolve(), '--bound-result', '--plan-only',
            '--jobs', 2, '--cpus', args.cpus], True)
        cases = {'unrelated_backend': 'actual final consumer',
                 'forged_modules': 'exact completed mathematical population',
                 'forged_lock': 'exact preserved source lock',
                 'forged_frontend': 'current and executed frontend',
                 'forged_helper': 'current and executed proof acceptance',
                 'forged_module_census': 'every exact locked application module',
                 'duplicate_json': 'duplicate JSON key', 'nonfinite_json': 'nonfinite JSON'}
        for case, reason in cases.items():
            directory = out / (mode + '-' + case)
            directory.mkdir()
            if case == 'forged_module_census':
                build = directory / 'build'
                build.mkdir()
                for name in ['RESULT.json', 'controller.py']:
                    shutil.copyfile(unrelated / name, build / name)
                plan = strict_json(unrelated / 'PLAN.json')
                plan.update(targets=[lock['root']], selected_theorems=lock['theorems'])
                (build / 'PLAN.json').write_text(json.dumps(plan))
            else:
                (directory / 'build').symlink_to(unrelated, target_is_directory=True)
            shutil.copyfile(front, directory / 'frontend.py')
            (directory / 'PREPARED.json').write_text(json.dumps(
                {'modules': 549, 'source_lock_sha256': sha(lock_path)}))
            receipt = {'status': 'COMPLETE_CLEAN_PACKED_MILLION_SOURCE_REPLAY', 'modules': 549,
                       'source_lock_sha256': sha(lock_path), 'script_sha256': sha(front),
                       'helper_sha256': sha(helper), 'build_result_sha256': sha(unrelated / 'RESULT.json')}
            if case == 'forged_modules':
                receipt['modules'] = 5480
            if case == 'forged_lock':
                receipt['source_lock_sha256'] = '0' * 64
            if case == 'forged_frontend':
                receipt['script_sha256'] = '0' * 64
            if case == 'forged_helper':
                receipt['helper_sha256'] = '0' * 64
            body = json.dumps(receipt)
            if case == 'duplicate_json':
                body = body[:-1] + ',"modules":549}'
            if case == 'nonfinite_json':
                body = body[:-1] + ',"bad":1e999}'
            (directory / 'RESULT.json').write_text(body)
            execute(mode, flags, case, [front, '--check', directory], False, reason)
    need(sha(front) == sha(out / 'frontend.py'), 'frontend source stable for all actual controls')
    result = {'status': 'PASS_ALL27_ACTUAL_NORMAL_O_OO_STAGING_AND_COMPLETED_SCOPE_CONTROLS',
              'frontend_sha256': sha(front), 'test_script_sha256': sha(Path(__file__)),
              'rows': rows, 'full_fresh_positive_check_is_separate': True}
    (out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['frontend_sha256'], flush=True)


if __name__ == '__main__':
    main()
