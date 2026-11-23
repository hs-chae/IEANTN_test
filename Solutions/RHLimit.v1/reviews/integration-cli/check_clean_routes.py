#!/usr/bin/env python3
"""Actual clean261+55 preflight and unsupported resource override controls."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time

FINAL_SHA = '857ba8bf9f670e5df415dba16c84cf72c3168c6aa49df0cf1649bdd7f1d404cf'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['controller', 'basis', 'spectral', 'resource', 'out']:
        p.add_argument('--' + name, type=Path, required=True)
    a = p.parse_args()
    need(not a.out.exists() and sha(a.controller) == FINAL_SHA, 'fresh output and exact final controller')
    basis = json.loads((a.basis / 'RESULT.json').read_bytes())
    need(basis.get('resource_complete_default_recipe') is True, 'actual resource-complete basis required')
    before = {str(f): sha(f) for d in [a.basis, a.spectral, a.resource]
              for f in d.rglob('*') if f.is_file() and not f.is_symlink()
              and 'union' not in f.relative_to(d).parts}
    a.out.mkdir(parents=True)
    rows = []
    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        for override in [False, True]:
            tag = mode + ('-override' if override else '-clean')
            target = a.out / ('unused-' + tag)
            cmd = [sys.executable, *flags, str(a.controller), '--basis', str(a.basis),
                   '--spectral', str(a.spectral), '--out', str(target), '--check']
            if override:
                cmd += ['--resource-replay', str(a.resource)]
            env = os.environ.copy()
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            began = time.monotonic()
            cp = subprocess.run(cmd, capture_output=True, text=True, env=env)
            (a.out / (tag + '.stdout')).write_text(cp.stdout)
            (a.out / (tag + '.stderr')).write_text(cp.stderr)
            if override:
                need(cp.returncode != 0 and 'resource replay is only supported for historicaltwo-stagebasis' in cp.stderr,
                     'clean override was not refused by its policy guard')
            else:
                need(cp.returncode == 0 and cp.stdout.strip() == 'PASS_COMPLETE_FRESH316_AND_FINAL24_SOURCE_PREFLIGHT',
                     'actual clean preflight failed: ' + cp.stderr)
            need(not target.exists(), 'check route created output')
            rows.append({'mode': mode, 'resource_override': override, 'command': cmd,
                         'returncode': cp.returncode, 'seconds': time.monotonic() - began,
                         'stdout_sha256': sha(a.out / (tag + '.stdout')),
                         'stderr_sha256': sha(a.out / (tag + '.stderr'))})
    need(all(sha(Path(path)) == h for path, h in before.items()), 'retained clean/bank input changed')
    result = {'status': 'PASS_ACTUAL_CLEAN3_PREFLIGHTS_AND_OVERRIDE3_REJECTIONS',
              'controller_sha256': FINAL_SHA, 'test_controller_sha256': sha(__file__),
              'basis_RESULT_sha256': sha(a.basis / 'RESULT.json'),
              'spectral_RESULT_sha256': sha(a.spectral / 'RESULT.json'),
              'retained_inputs_unchanged': True, 'retained_files_checked': len(before),
              'actual_clean_policy_flag': True, 'private_fixture_policy_override': False, 'routes': rows}
    pending = a.out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, a.out / 'RESULT.json')
    print(result['status'])


if __name__ == '__main__':
    main()
