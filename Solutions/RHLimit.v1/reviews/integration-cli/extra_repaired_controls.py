#!/usr/bin/env python3
"""Actual CLI negatives for the newly added legacy source/log/C/controller joins."""
from pathlib import Path
import hashlib, importlib.util, json, os, subprocess, sys, time

B = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('fixture_tools', B / 'run_controls_repaired.py')
u = importlib.util.module_from_spec(spec)
spec.loader.exec_module(u)


def main():
    out = B / 'repaired-extra-v1'
    u.need(not out.exists(), 'fresh output')
    out.mkdir()
    cases = [
        ('stderr-bytes', 'resource logs'),
        ('C-include-bytes', 'resource C include identity'),
        ('executed-controller-bytes', 'resource controller identity'),
        ('RESULT-controller-field', 'resource controller identity'),
        ('RESULT-default-controller-field', 'resource default controller identity'),
        ('RESULT-source-manifest-field', 'resource source manifest'),
        ('RESULT-basis-BUILD-field', 'resource basis BUILD association'),
        ('BUILD-source-field', 'resource source identity'),
        ('BUILD-module-order', 'resource replay object'),
        ('BUILD-status', 'resource replay BUILD'),
    ]
    rows = []
    started = time.monotonic()
    for name, expected in cases:
        case = out / name
        u.clone(B / 'repaired-spec-v1/pristine', case)
        rr, rb = case / 'resources/RESULT.json', case / 'resources/BUILD.json'
        module = u.read(rb)['modules'][0]['module']
        if name == 'stderr-bytes':
            f = case / 'resources/logs' / (module + '.stderr')
            u.atomic_bytes(f, f.read_bytes() + b'\nfixture stderr drift\n')
        elif name == 'C-include-bytes':
            f = case / 'resources/source/c/verified_finite_log.c'
            u.atomic_bytes(f, f.read_bytes() + b'\n/* fixture C byte drift */\n')
        elif name == 'executed-controller-bytes':
            f = case / 'resources/reproduce.executed.py'
            u.atomic_bytes(f, f.read_bytes() + b'\n# fixture controller drift\n')
        elif name.startswith('RESULT-'):
            key = {'RESULT-controller-field': 'controller_sha256',
                   'RESULT-default-controller-field': 'default_complete_controller_sha256',
                   'RESULT-source-manifest-field': 'source_manifest_sha256',
                   'RESULT-basis-BUILD-field': 'basis_BUILD_sha256'}[name]
            u.change_json(rr, lambda j: j.update({key: '0' * 64}))
        else:
            def edit(j):
                if name == 'BUILD-source-field':
                    j['modules'][0]['source_sha256'] = '0' * 64
                elif name == 'BUILD-module-order':
                    j['modules'][0], j['modules'][1] = j['modules'][1], j['modules'][0]
                else:
                    j['status'] = 'RUNNING'
            u.change_json(rb, edit)
            u.change_json(rr, lambda j: j.update(BUILD_sha256=u.sha(rb)))
        u.change_json(case / 'spectral/RESULT.json',
                      lambda j: j.update(resource23_RESULT_sha256=u.sha(rr)))
        controller = case / 'network/Solutions/RHLimit.v1/scripts/reproduce_integration.py'
        u.need(u.sha(controller) == u.EXPECTED_CONTROLLER, 'actual revised CLI identity')
        for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
            target = case / ('unused-' + mode)
            cmd = [sys.executable, *flags, str(controller), '--basis', str(case / 'pi'),
                   '--spectral', str(case / 'spectral'), '--resource-replay', str(case / 'resources'),
                   '--out', str(target), '--check']
            env = os.environ.copy()
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            cp = subprocess.run(cmd, capture_output=True, text=True, env=env)
            (case / (mode + '.stdout')).write_text(cp.stdout)
            (case / (mode + '.stderr')).write_text(cp.stderr)
            u.need(cp.returncode != 0 and expected in cp.stderr and not target.exists(),
                   'actual revised guard failure: ' + name + ' ' + mode)
            rows.append({'case': name, 'mode': mode, 'command': cmd, 'returncode': cp.returncode,
                         'expected_rejection': expected, 'stdout_sha256': u.sha(case / (mode + '.stdout')),
                         'stderr_sha256': u.sha(case / (mode + '.stderr'))})
            print(name, mode, 'PASS_EXPECTED_REJECTION', flush=True)
    originals = u.read(B / 'fixed-spec-v2/ORIGINAL_INPUTS_BEFORE.json')
    u.need(all(u.sha(Path(path)) == digest for path, digest in originals.items()), 'retained inputs changed')
    result = {'status': 'PASS_ALL30_NEW_LEGACY_JOIN_ACTUAL_CLI_REJECTIONS_NORMAL_O_OO',
              'controller_sha256': u.EXPECTED_CONTROLLER, 'test_controller_sha256': u.sha(__file__),
              'rows': rows, 'seconds': time.monotonic() - started,
              'retained_original_inputs_unchanged': True, 'retained_inputs_checked': len(originals),
              'source_specification_changed': False}
    pending = out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, out / 'RESULT.json')
    print(result['status'], flush=True)


if __name__ == '__main__':
    main()
