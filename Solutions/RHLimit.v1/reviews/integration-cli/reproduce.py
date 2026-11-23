#!/usr/bin/env python3
"""Reproduce the original63 and repaired93 actual integration CLI controls.

Only private fixture metadata is rebased to exercise the optional legacy branch.
No numerical output, mathematical source or retained proof-bank file is changed.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys

E = Path(__file__).resolve().parent
spec = __import__('importlib.util', fromlist=['util'])
ms = spec.spec_from_file_location('fixture_tools', E / 'run_controls.py')
u = spec.module_from_spec(ms)
ms.loader.exec_module(u)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    for key in ['network', 'pi', 'resources', 'spectral', 'out']:
        p.add_argument('--' + key, required=True, type=Path)
    a = p.parse_args()
    out = a.out.resolve()
    u.need(out.is_relative_to(u.DEFAULT_D / 'reviews/integration-cli') and not out.exists(), 'fresh owned scratch')
    inputs = json.loads((E / 'LOCKED_SOURCE_INPUTS.json').read_bytes())
    out.mkdir(parents=True)
    original = out / 'source-original/network'
    special = 'Solutions/RHLimit.v1/scripts/reproduce_integration.py'
    for row in inputs:
        src, dst = a.network / row['path'], original / row['path']
        if row['path'] == special:
            src = E / 'controllers/integration.original.py'
        else:
            u.need(u.sha(src) == row['sha256'], 'approved source snapshot differs: ' + row['path'])
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
    repaired = out / 'source-repaired/network'
    u.clone(original, repaired)
    u.atomic_bytes(repaired / special, (E / 'controllers/integration.final.py').read_bytes())
    banks = out / 'banks'
    for source, rel in [(a.pi, 'pi/cold261-v1'), (a.resources, 'pi/resource23-v1'),
                        (a.spectral, 'spectral/cold55-v1')]:
        u.clone(source, banks / rel)
    # This private counterfactual selects the optional legacy route even when
    # the caller regenerated a resource-complete default prefix. It is not a
    # relabeling or mutation of the original experimental outcome.
    pi, rr, sr = [banks / x for x in ['pi/cold261-v1/RESULT.json', 'pi/resource23-v1/RESULT.json',
                                     'spectral/cold55-v1/RESULT.json']]
    u.change_json(pi, lambda j: j.update(resource_complete_default_recipe=False))
    u.change_json(rr, lambda j: j.update(basis_RESULT_sha256=u.sha(pi),
                                        basis_BUILD_sha256=u.sha(banks / 'pi/cold261-v1/BUILD.json')))
    u.change_json(sr, lambda j: j.update(basis_RESULT_sha256=u.sha(pi),
                                        basis_BUILD_sha256=u.sha(banks / 'pi/cold261-v1/BUILD.json'),
                                        resource23_RESULT_sha256=u.sha(rr)))
    for name in ['run_controls.py', 'run_controls_final.py', 'extra_final_controls.py']:
        shutil.copy2(E / name, out / name)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    commands = [
        [sys.executable, str(out / 'run_controls.py'), '--network', str(original), '--data', str(banks),
         '--out', str(out / 'fixed-spec-v2')],
        [sys.executable, str(out / 'run_controls_final.py'), '--network', str(repaired), '--data', str(banks),
         '--out', str(out / 'final-spec-v1')],
        [sys.executable, str(out / 'extra_final_controls.py')]]
    # The extra controls check hashes of the retained proof banks supplied to
    # the copied harness; all mutations use fresh inodes in deeper fixtures.
    rows = []
    for index, cmd in enumerate(commands):
        cp = subprocess.run(cmd, capture_output=True, text=True, env=env)
        (out / ('stage' + str(index) + '.stdout')).write_text(cp.stdout)
        (out / ('stage' + str(index) + '.stderr')).write_text(cp.stderr)
        u.need(cp.returncode == 0, 'actual matrix reproduction failed: ' + cp.stdout + cp.stderr)
        rows.append({'command': cmd, 'returncode': cp.returncode})
    old = u.read(out / 'fixed-spec-v2/RESULT.json')
    new = u.read(out / 'final-spec-v1/RESULT.json')
    extra = u.read(out / 'final-extra-v1/RESULT.json')
    u.need(len(old['findings']) == 6 and len(old['routes']) == 63, 'original six acceptances not reproduced')
    u.need(not new['findings'] and len(new['routes']) == 63, 'repaired63 did not pass')
    u.need(len(extra['rows']) == 30, 'new joins30 incomplete')
    result = {'status': 'PASS_REPRODUCED_ORIGINAL6_ACCEPTANCES_AND_REPAIRED93_ROUTES',
              'commands': rows, 'private_legacy_policy_fixture_only': True,
              'original_experimental_outcomes_changed': False,
              'mathematical_sources_or_numerical_outputs_changed': False,
              'original63_RESULT_sha256': u.sha(out / 'fixed-spec-v2/RESULT.json'),
              'repaired63_RESULT_sha256': u.sha(out / 'final-spec-v1/RESULT.json'),
              'extra30_RESULT_sha256': u.sha(out / 'final-extra-v1/RESULT.json')}
    (out / 'REPRODUCTION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
