#!/usr/bin/env python3
"""Actual integration CLI controls in private fixtures; retained inputs immutable."""
from pathlib import Path
import argparse, errno, hashlib, json, os, shutil, subprocess, sys, time

DEFAULT_N = Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-continuation-20261122/network')
DEFAULT_D = Path('/data/ivy-rh-limit-20261122')
EXPECTED_CONTROLLER = '4374e647a008568d2450fe5c46354cebacdf109866072db6445500f9c8078dbf'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def atomic_bytes(path, value):
    """Create a NEW inode and replace a fixture file, never write a hardlink."""
    path = Path(path)
    need(not path.is_symlink(), 'refuse symlink mutation')
    pending = path.with_name('.' + path.name + '.private-pending')
    need(not pending.exists(), 'fresh private replacement')
    pending.write_bytes(value)
    need(pending.stat().st_nlink == 1, 'private replacement inode')
    os.replace(pending, path)
    need(path.stat().st_nlink == 1, 'fixture detach failed')


def change_json(path, edit):
    value = read(path)
    edit(value)
    atomic_bytes(path, (json.dumps(value, indent=2) + '\n').encode())


def link_or_copy(src, dst):
    try:
        return os.link(src, dst)
    except OSError as ex:
        if ex.errno != errno.EXDEV:
            raise
        return shutil.copy2(src, dst)


def clone(src, dst):
    shutil.copytree(src, dst, copy_function=link_or_copy, symlinks=True,
                    ignore=lambda _p, names: [n for n in names if n in {'union', '__pycache__'}])


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--network', type=Path, default=DEFAULT_N)
    p.add_argument('--data', type=Path, default=DEFAULT_D)
    a = p.parse_args()
    out = a.out.resolve()
    need(out.is_relative_to(DEFAULT_D / 'reviews/integration-cli') and not out.exists(), 'fresh owned output')
    out.mkdir(parents=True)
    n, s = a.network.resolve(), a.network.resolve() / 'Solutions/RHLimit.v1'
    need(sha(s / 'scripts/reproduce_integration.py') == EXPECTED_CONTROLLER, 'actual controller identity')
    retained = {'pi': a.data / 'pi/cold261-v1', 'resources': a.data / 'pi/resource23-v1',
                'spectral': a.data / 'spectral/cold55-v1'}
    required = set()
    for folder in ['pi', 'spectral', 'integration']:
        required.add('Solutions/RHLimit.v1/' + folder + '/SOURCE_CLOSURE.json')
        for row in read(s / folder / 'SOURCE_CLOSURE.json')['modules']:
            required.add(row['path'])
            if 'original_path' in row:
                required.add(row['original_path'])
    for rel in ['scripts/reproduce_integration.py', 'scripts/reproduce_pi_resources.py',
                'scripts/reproduce_pi_complete.py', 'spectral/reproduce_cold_append.py',
                'pi/RESOURCES.json', 'pi/RESOURCE_CLOSURE.json', 'spectral/frozen-source/rh_coeff.c']:
        required.add('Solutions/RHLimit.v1/' + rel)
    for row in read(s / 'pi/RESOURCES.json')['resources']:
        required.add(row['path'])
    originals = [n / rel for rel in sorted(required)]
    for folder in retained.values():
        originals += [x for x in sorted(folder.rglob('*')) if x.is_file() and not x.is_symlink()
                      and 'union' not in x.relative_to(folder).parts and '__pycache__' not in x.parts]
    before = {str(x): sha(x) for x in originals}
    (out / 'ORIGINAL_INPUTS_BEFORE.json').write_text(json.dumps(before, indent=2) + '\n')
    pristine = out / 'pristine'
    fn = pristine / 'network'
    fs = fn / 'Solutions/RHLimit.v1'
    for rel in sorted(required):
        target = fn / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        link_or_copy(n / rel, target)
    for name, folder in retained.items():
        clone(folder, pristine / name)
    cases = [
        ('positive', None),
        ('wrong-basis-status', 'complete source basis required'),
        ('duplicate-json', 'duplicate JSON key'),
        ('nonfinite-json', 'nonfinite JSON'),
        ('basis-False-rehashed', 'basis actual compiler status'),
        ('spectral-False-rehashed', 'spectral compiler status'),
        ('resource-False-rehashed', 'resource replay object'),
        ('basis-source', 'basis source identity'),
        ('basis-object', 'basis object identity'),
        ('basis-log', 'basis logs'),
        ('spectral-source', 'spectral source'),
        ('spectral-object', 'spectral object'),
        ('spectral-log', 'spectral logs'),
        ('resource-source', 'resource source identity'),
        ('resource-object', 'resource replay object'),
        ('resource-log', 'resource logs'),
        ('canonical-current-source', 'current public canonical source drift'),
        ('canonical-current-missing', 'FileNotFoundError'),
        ('missing-resource-replay', 'initial two-stage source run needs explicit independent23resource replay'),
        ('existing-output', 'fresh output required'),
        ('unknown-option', 'unrecognized arguments'),
    ]
    rows, findings = [], []
    started = time.monotonic()
    for name, expected in cases:
        case = out / 'cases' / name
        clone(pristine, case)
        cn, cs = case / 'network', case / 'network/Solutions/RHLimit.v1'
        if name == 'wrong-basis-status':
            change_json(case / 'pi/RESULT.json', lambda j: j.update(status='NOT_PASS'))
        elif name == 'duplicate-json':
            f = case / 'pi/RESULT.json'
            atomic_bytes(f, b'{"status":"DUPLICATE",' + f.read_bytes().lstrip()[1:])
        elif name == 'nonfinite-json':
            change_json(case / 'pi/RESULT.json', lambda j: j.update(invalid=float('nan')))
        elif 'False-rehashed' in name:
            bank = {'basis-False-rehashed': 'pi', 'spectral-False-rehashed': 'spectral',
                    'resource-False-rehashed': 'resources'}[name]
            build = case / bank / 'BUILD.json'
            change_json(build, lambda j: j['modules'][0].update(returncode=False))
            change_json(case / bank / 'RESULT.json', lambda j: j.update(BUILD_sha256=sha(build)))
            if bank == 'resources':
                change_json(case / 'spectral/RESULT.json',
                            lambda j: j.update(resource23_RESULT_sha256=sha(case / 'resources/RESULT.json')))
        elif name.split('-')[0] in {'basis', 'spectral', 'resource'}:
            bank = {'basis': 'pi', 'spectral': 'spectral', 'resource': 'resources'}[name.split('-')[0]]
            row = read(case / bank / 'BUILD.json')['modules'][0]
            suffix = name.split('-')[1]
            mod = row['module']
            if suffix == 'source':
                f = case / bank / 'source' / (mod.replace('.', '/') + '.lean')
            elif suffix == 'object':
                f = case / bank / 'objects' / (mod.replace('.', '/') + '.olean')
            else:
                f = case / bank / 'logs' / (mod + '.stdout')
            atomic_bytes(f, f.read_bytes() + b'\nfixture altered bytes\n')
        elif name.startswith('canonical-current'):
            spec = read(cs / 'integration/SOURCE_CLOSURE.json')
            rel = next(row['original_path'] for row in spec['modules'] if 'original_path' in row)
            f = cn / rel
            if name.endswith('missing'):
                f.unlink()
            else:
                atomic_bytes(f, f.read_bytes() + b'\n-- fixture current source drift\n')
        elif name == 'existing-output':
            (case / 'existing-out').mkdir()
            (case / 'existing-out/sentinel').write_text('must remain unchanged\n')
        controller = cs / 'scripts/reproduce_integration.py'
        need(sha(controller) == EXPECTED_CONTROLLER, 'fixture actual CLI bytes')
        for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
            target = case / ('unused-' + mode) if name != 'existing-output' else case / 'existing-out'
            cmd = [sys.executable, *flags, str(controller), '--basis', str(case / 'pi'),
                   '--spectral', str(case / 'spectral'), '--out', str(target), '--check']
            if name != 'missing-resource-replay':
                cmd += ['--resource-replay', str(case / 'resources')]
            if name == 'unknown-option':
                cmd += ['--not-an-integration-option']
            env = os.environ.copy()
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            t = time.monotonic()
            cp = subprocess.run(cmd, env=env, capture_output=True, text=True)
            (case / (mode + '.stdout')).write_text(cp.stdout)
            (case / (mode + '.stderr')).write_text(cp.stderr)
            accepted = cp.returncode == 0 and cp.stdout.strip() == 'PASS_COMPLETE_FRESH316_AND_FINAL24_SOURCE_PREFLIGHT'
            if expected is None:
                ok = accepted and not target.exists()
            else:
                ok = cp.returncode != 0 and expected in cp.stderr and not (
                    name != 'existing-output' and target.exists())
            disposition = 'PASS_EXPECTED_ROUTE' if ok else ('UNEXPECTED_ACCEPTANCE' if accepted else 'WRONG_GUARD_OR_FIXTURE_FAILURE')
            rr = {'case': name, 'mode': mode, 'command': cmd, 'returncode': cp.returncode,
                  'seconds': time.monotonic() - t, 'accepted': accepted,
                  'expected_rejection': expected, 'disposition': disposition,
                  'stdout_sha256': sha(case / (mode + '.stdout')),
                  'stderr_sha256': sha(case / (mode + '.stderr')),
                  'environment': {'PYTHONDONTWRITEBYTECODE': '1'}}
            rows.append(rr)
            if not ok:
                findings.append(rr)
            print(name, mode, disposition, flush=True)
    after = {str(x): sha(x) for x in originals}
    need(before == after, 'retained source/bank mutation detected')
    (out / 'ORIGINAL_INPUTS_AFTER.json').write_text(json.dumps(after, indent=2) + '\n')
    result = {'status': 'PASS_ALL63_ACTUAL_INTEGRATION_CLI_ROUTES' if not findings else 'ACTUAL_CLI_ACCEPTANCE_FINDINGS',
              'controller_sha256': EXPECTED_CONTROLLER, 'fixture_controller_bytes_identical': True,
              'test_controller_sha256': sha(__file__), 'routes': rows, 'findings': findings,
              'retained_inputs_unchanged': True, 'retained_inputs_checked': len(before),
              'seconds': time.monotonic() - started,
              'source_specification_changed': False, 'mathematical_sources_changed': False,
              'scope': 'Actual --check receipt/source/object/log guards under fixed approved source specification; no new mathematical proof or source-first PV claim.'}
    pending = out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, out / 'RESULT.json')
    print(result['status'], 'findings', len(findings), flush=True)


if __name__ == '__main__':
    main()
