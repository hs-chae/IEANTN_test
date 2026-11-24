#!/usr/bin/env python3
"""Exercise actual readback CLIs in all Python optimization modes.

Mutations touch only fresh owned copies. The accepted replay is read-only.
All mutation evidence is retained; duplicated regenerable objects are removed
only after every control has been checked and their cleanup paths validated.
"""
from pathlib import Path
import argparse, concurrent.futures as cf, hashlib, json, shutil, subprocess, sys, time

H = Path(__file__).resolve().parent
CONTROLLER = H/'reproduce_zero.py'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write(path, data):
    path.write_text(json.dumps(data, indent=2, allow_nan=False)+'\n')

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    run, out = a.run.resolve(), a.out.resolve()
    need(run.is_dir() and (run/'RESULT.json').is_file(), 'completed original required')
    need(not out.exists(), 'fresh controls namespace required')
    out.mkdir()
    controller_hash, result_hash = sha(CONTROLLER), sha(run/'RESULT.json')
    cases = []
    for optimization in range(3):
        cases.append((optimization, 'valid'))
        cases.append((optimization, 'source_mutation'))
        cases.append((optimization, 'object_mutation'))
        cases.append((optimization, 'foreign_dependency'))
        cases.append((optimization, 'nonstandard_axiom'))
        cases.append((optimization, 'duplicate_json_key'))
    cases.append((0, 'relocated_valid'))

    def one(item):
        optimization, name = item
        directory = out/(str(optimization)+'-'+name)
        directory.mkdir()
        mutant = directory/'copy'
        target = run
        if name != 'valid':
            shutil.copytree(run, mutant, symlinks=True)
            target = mutant
        evidence = {'case': name, 'optimization': optimization,
                    'original_RESULT_sha256': result_hash}
        if name == 'source_mutation':
            path = mutant/'source/BoxZeroEstimate.lean'
            path.write_bytes(path.read_bytes()+b'\n-- adversarial source byte mutation\n')
            evidence['mutated_source_sha256'] = sha(path)
        elif name == 'object_mutation':
            path = mutant/'objects/BoxZeroEstimate.olean'
            path.write_bytes(path.read_bytes()+b'UNACCEPTED_OBJECT_MUTATION')
            evidence['mutated_object_sha256'] = sha(path)
        elif name == 'foreign_dependency':
            rr = json.loads((mutant/'RESULT.json').read_text())
            probe = rr['dependency_probes'][-1]
            path = mutant/'dependencies'/probe['stdout']
            path.write_text(path.read_text().rstrip('\n')+'\n/etc/hosts\n')
            probe['stdout_sha256'] = sha(path)
            write(mutant/'RESULT.json', rr)
            evidence['mutated_probe_sha256'] = sha(path)
        elif name == 'nonstandard_axiom':
            rr = json.loads((mutant/'RESULT.json').read_text())
            build = json.loads((mutant/'BUILD.json').read_text())
            path = mutant/'logs/FinalBoxZeroAudit.stdout'
            text = path.read_text()
            need('"axioms":[' in text, 'actual theorem audit evidence')
            path.write_text(text.replace('"axioms":[', '"axioms":["Lean.ofReduceBool",', 1))
            build['modules'][-1]['stdout_sha256'] = sha(path)
            write(mutant/'BUILD.json', build)
            rr['BUILD_sha256'] = sha(mutant/'BUILD.json')
            write(mutant/'RESULT.json', rr)
            evidence['mutated_audit_sha256'] = sha(path)
        elif name == 'duplicate_json_key':
            path = mutant/'RESULT.json'
            text = path.read_text()
            path.write_text('{"status":"UNACCEPTED_DUPLICATE",'+text[1:])
            evidence['mutated_RESULT_sha256'] = sha(path)
        command = [sys.executable]+(['-'+('O'*optimization)] if optimization else [])
        command += [str(CONTROLLER), '--verify', str(target)]
        started = time.monotonic()
        cp = subprocess.run(command, capture_output=True, text=True)
        (directory/'stdout').write_text(cp.stdout)
        (directory/'stderr').write_text(cp.stderr)
        positive = name in ['valid', 'relocated_valid']
        need((cp.returncode == 0) == positive, 'incorrect actual CLI acceptance:'+str(item))
        if positive:
            result = json.loads(cp.stdout)
            need(result['status'] == 'PASS_BOX40_READBACK'
                 and result['optimization'] == optimization, 'positive CLI status')
        else:
            expected = {
                'source_mutation': 'source/object association',
                'object_mutation': 'source/object association',
                'foreign_dependency': 'foreign or drifted application object',
                'nonstandard_axiom': 'nonstandard proof axiom or foreign theorem',
                'duplicate_json_key': 'duplicate JSON key',
            }[name]
            need(expected in cp.stderr, 'mutation rejected at an unintended gate:'+str(item))
            evidence['expected_error'] = expected
        evidence.update({'status': 'PASS_EXPECTED_ACCEPT' if positive else 'PASS_EXPECTED_REJECT',
                         'command': command, 'returncode': cp.returncode,
                         'seconds': time.monotonic()-started,
                         'stdout_sha256': sha(directory/'stdout'),
                         'stderr_sha256': sha(directory/'stderr')})
        if mutant.exists():
            # Preserve changed minimal text evidence and original association,
            # not nineteen redundant copies of the accepted proof object bank.
            for relative in ['RESULT.json', 'BUILD.json']:
                (directory/('mutant-'+relative)).write_bytes((mutant/relative).read_bytes())
            if name == 'source_mutation':
                (directory/'mutant-source.lean').write_bytes(
                    (mutant/'source/BoxZeroEstimate.lean').read_bytes())
            if name == 'foreign_dependency':
                (directory/'mutant-dependencies').write_bytes(path.read_bytes())
            if name == 'nonstandard_axiom':
                (directory/'mutant-audit.stdout').write_bytes(path.read_bytes())
            need(mutant.parent == directory and directory.parent == out
                 and mutant.name == 'copy' and not mutant.is_symlink()
                 and (mutant/'source/BoxZeroEstimate.lean').is_file(), 'verified cleanup scope')
            shutil.rmtree(mutant)
            evidence['cleanup'] = (
                'Verified experiment-owned duplicate copy removed after checked control; '
                'accepted original and minimal mutation evidence retained.')
        write(directory/'CONTROL.json', evidence)
        print(optimization, name, evidence['status'], flush=True)
        return evidence

    with cf.ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(one, cases))
    need(sha(CONTROLLER) == controller_hash and sha(run/'RESULT.json') == result_hash,
         'controller or original acceptance changed during controls')
    result = {'status': 'PASS_ALL19_BOX40_CLI_CONTROLS', 'controller_sha256': controller_hash,
              'controls_controller_sha256': sha(__file__), 'original_RESULT_sha256': result_hash,
              'cases': results, 'optimization_modes': [0, 1, 2],
              'acceptance_assert_or_debug_used': False,
              'cleanup': 'Only fresh per-control duplicate copies were deleted after explicit scope checks.'}
    candidate = out/'CANDIDATE.json'
    write(candidate, result)
    candidate.replace(out/'RESULT.json')
    print(result['status'])

if __name__ == '__main__':
    main()
