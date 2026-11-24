#!/usr/bin/env python3
"""Actual positive/negative CLI controls for the additive fresh32 readback."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
CHECKER = HERE/'readback_complete.py'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--basis', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    basis, out = args.basis.resolve(), args.out.resolve()
    need(basis.is_dir() and not out.exists(), 'existing basis and fresh owned control directory')
    need(not out.is_relative_to(basis), 'control output must be outside accepted basis')
    original = json.loads((basis/'RESULT.json').read_text())
    names = [q['module'] for q in original['build']]
    first = original['source_plan']['modules'][0]['module']
    source_name = Path(*first.split('.')).with_suffix('.lean')
    resource = original['source_plan']['resources'][0]['relative']
    negative = ['copied_source_rehashed', 'copied_C_resource_changed', 'missing_C_resource',
                'audit_source_rehashed', 'empty_dependencies_rehashed',
                'dropped_direct_import_rehashed', 'foreign_dependency_rehashed',
                'false_compiler_status', 'float_compiler_status', 'false_duration',
                'changed_context', 'context_false_zero', 'historical_cache_claim',
                'numerical_claim', 'duplicate_JSON_key', 'symlink_resource',
                'duplicate_proof_payload', 'overflow_duration']
    expected_error = {
        'copied_source_rehashed': 'copied source bound to frozen scientific plan',
        'copied_C_resource_changed': 'copied actual C resource',
        'missing_C_resource': 'owned copied C resource',
        'audit_source_rehashed': 'complete generated theorem auditor',
        'empty_dependencies_rehashed': 'nonempty actual dependency closure',
        'dropped_direct_import_rehashed': 'actual application import coverage',
        'foreign_dependency_rehashed': 'foreign application object admitted',
        'false_compiler_status': 'actual compiler status',
        'float_compiler_status': 'actual compiler status',
        'false_duration': 'actual finite nonnegative compiler duration',
        'changed_context': 'approved generic context',
        'context_false_zero': 'approved generic context',
        'historical_cache_claim': 'fresh application objects',
        'numerical_claim': 'explicit trust/numerical boundaries',
        'duplicate_JSON_key': 'duplicate JSON key',
        'symlink_resource': 'owned copied C resource',
        'duplicate_proof_payload': 'duplicate JSON key',
        'overflow_duration': 'nonfinite JSON number'}
    out.mkdir()
    cases = []
    started = time.monotonic()
    checker_sha = sha(CHECKER)
    for flags in [[], ['-O'], ['-OO']]:
        forbidden = basis/'nested-control-output-must-remain-absent'
        need(not forbidden.exists(), 'fresh forbidden-output boundary control')
        command = [sys.executable, *flags, str(Path(__file__).resolve()),
                   '--basis', str(basis), '--out', str(forbidden)]
        cp = subprocess.run(command, capture_output=True, text=True)
        need(cp.returncode != 0 and 'control output must be outside accepted basis' in cp.stderr,
             'actual nested-output rejection gate')
        need(not forbidden.exists(), 'nested-output rejection precedes all writes')
        label = 'nested-output-mode'+str(len(flags) and len(flags[0])-1 or 0)
        (out/(label+'.stdout')).write_text(cp.stdout)
        (out/(label+'.stderr')).write_text(cp.stderr)
        cases.append(dict(case='nested_output_boundary', flags=flags, command=command,
                          returncode=cp.returncode, receipt_written=False,
                          expected_rejection='control output must be outside accepted basis',
                          stdout_sha256=sha(out/(label+'.stdout')),
                          stderr_sha256=sha(out/(label+'.stderr'))))
    for flags in [[], ['-O'], ['-OO']]:
        for name in ['positive']+negative:
            case = out/('mode'+str(len(flags) and len(flags[0])-1 or 0)+'_'+name)
            shutil.copytree(basis, case)
            # A relocated positive fixture has the same files and execution
            # commands it would have generated at this fresh owned location.
            report = json.loads((case/'RESULT.json').read_text())
            for row in report['build']:
                row['command'] = [x.replace(str(basis), str(case)) for x in row['command']]
            for probe in report['dependencies']:
                probe['command'] = [x.replace(str(basis), str(case)) for x in probe['command']]
                path = case/'dependencies'/(probe['module']+'.stdout')
                path.write_text(path.read_text().replace(str(basis), str(case)))
                probe['stdout_sha256'] = sha(path)
            def build(mod):
                return next(q for q in report['build'] if q['module'] == mod)
            def dep(mod):
                return next(q for q in report['dependencies'] if q['module'] == mod)
            if name == 'copied_source_rehashed':
                path = case/'source'/source_name
                path.write_text(path.read_text()+'\n-- adversarial source mutation\n')
                build(first)['source_sha256'] = sha(path)
            elif name == 'copied_C_resource_changed':
                path = case/'source'/resource
                path.write_bytes(path.read_bytes()+b'\n/* altered copied C */\n')
            elif name == 'missing_C_resource':
                (case/'source'/resource).unlink()
            elif name == 'audit_source_rehashed':
                path = case/'source/HighApplicationAudit.lean'
                path.write_text(path.read_text().replace('  let mods := #[',
                                                       '  let mods := #[] -- ', 1))
                build('HighApplicationAudit')['source_sha256'] = sha(path)
            elif name in ['empty_dependencies_rehashed', 'dropped_direct_import_rehashed',
                          'foreign_dependency_rehashed']:
                mod = 'HighDriverContract'
                path = case/'dependencies'/(mod+'.stdout')
                if name == 'empty_dependencies_rehashed':
                    path.write_text('')
                elif name == 'dropped_direct_import_rehashed':
                    path.write_text('\n'.join(x for x in path.read_text().splitlines()
                                             if not x.startswith(str(case)))+'\n')
                else:
                    path.write_text(path.read_text()+'/tmp/unrelated/Foreign.olean\n')
                dep(mod)['stdout_sha256'] = sha(path)
            elif name == 'false_compiler_status':
                report['build'][0]['returncode'] = False
            elif name == 'float_compiler_status':
                report['build'][0]['returncode'] = 0.0
            elif name == 'false_duration':
                report['build'][0]['seconds'] = False
            elif name == 'changed_context':
                report['context']['generic_libraries'].append('/tmp/unrelated')
            elif name == 'context_false_zero':
                report['context']['generic_dependencies'][0]['library_present'] = 1
            elif name == 'historical_cache_claim':
                report['historical_application_objects_used'] = True
            elif name == 'numerical_claim':
                report['exact_numerical_value_proved'] = True
            elif name == 'symlink_resource':
                path = case/'source'/resource
                path.unlink()
                path.symlink_to(basis/'source'/resource)
            elif name == 'duplicate_proof_payload':
                path = case/'logs/HighApplicationAudit.stdout'
                text = path.read_text().replace('HIGH_MAIN_PROOF {',
                    'HIGH_MAIN_PROOF {"axioms":["Lean.ofReduceBool"],', 1)
                path.write_text(text)
                build('HighApplicationAudit')['stdout_sha256'] = sha(path)
            elif name == 'overflow_duration':
                report['build'][0]['seconds'] = 1.0
            save(case/'RESULT.json', report)
            if name == 'duplicate_JSON_key':
                path = case/'RESULT.json'
                path.write_text(path.read_text().replace('{', '{"status":"forged",', 1))
            elif name == 'overflow_duration':
                path = case/'RESULT.json'
                path.write_text(path.read_text().replace('"seconds": 1.0',
                                                        '"seconds": 1e400', 1))
            receipt = out/(case.name+'.receipt.json')
            cmd = [sys.executable, *flags, str(CHECKER), '--verify', str(case),
                   '--receipt', str(receipt)]
            cp = subprocess.run(cmd, capture_output=True, text=True)
            (out/(case.name+'.stdout')).write_text(cp.stdout)
            (out/(case.name+'.stderr')).write_text(cp.stderr)
            need((cp.returncode == 0) == (name == 'positive'),
                 'unexpected actual CLI decision: '+case.name)
            need(receipt.exists() == (name == 'positive'), 'no receipt on rejected input')
            if name != 'positive':
                need(expected_error[name] in cp.stderr,
                     'wrong rejection gate: '+case.name+'\n'+cp.stderr)
            cases.append(dict(case=name, flags=flags, command=cmd, returncode=cp.returncode,
                              receipt_written=receipt.exists(),
                              expected_rejection=None if name == 'positive' else expected_error[name],
                              stdout_sha256=sha(out/(case.name+'.stdout')),
                              stderr_sha256=sha(out/(case.name+'.stderr'))))
            # Only a checked fresh control copy is removed; the accepted basis,
            # original sources, objects and receipts are never cleanup targets.
            need(case.parent == out and case.is_dir() and not case.is_symlink(),
                 'owned exact control copy cleanup')
            shutil.rmtree(case)
    need(sha(CHECKER) == checker_sha, 'source stable throughout actual controls')
    result = dict(status='PASS_ACTUAL_HIGH_APPLICATION_COMPLETE_READBACK_CONTROLS',
                  checker_sha256=checker_sha, test_source_sha256=sha(__file__),
                  basis_result_sha256=sha(basis/'RESULT.json'), cases=cases,
                  count=len(cases), positive_cases=3, rejected_mutations=len(negative)*3+3,
                  seconds=time.monotonic()-started, copied_regenerable_fixtures_removed=True,
                  original_basis_unchanged=True,
                  positives='Relocated synthetic validator fixtures; no recompilation is claimed.')
    pending = out/'RESULT.pending.json'
    save(pending, result)
    os.replace(pending, out/'RESULT.json')
    print(json.dumps({k:v for k,v in result.items() if k != 'cases'}))


if __name__ == '__main__':
    main()
