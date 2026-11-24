#!/usr/bin/env python3
"""Actual normal/-O/-OO dependency-inventory controls on an owned copy only."""
from pathlib import Path
import argparse, concurrent.futures as futures, hashlib, json, os, shutil, subprocess, sys

H = Path(__file__).resolve().parent

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--basis', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists(), 'fresh owned controls namespace')
    out.mkdir(parents=True)
    clone = out/'dependency-mutant'
    shutil.copytree(args.basis, clone, symlinks=True)
    receipt = json.loads((clone/'RESULT.json').read_text())
    probe = receipt['dependency_probes'][0]
    log = clone/'dependencies'/probe['stdout']
    need(log.is_file() and not log.is_symlink() and log.resolve().is_relative_to(clone),
         'owned regular mutation target')
    original_log_hash = sha(log)
    log.write_bytes(b'')
    probe['stdout_sha256'] = sha(log)
    (clone/'RESULT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    jobs = []
    for mode in [[], ['-O'], ['-OO']]:
        jobs.append(('prior-readback-empty-inventory', True, [sys.executable, *mode,
                     str(H.parent/'spectral_final/reproduce.py'), '--verify', str(clone)]))
        jobs.append(('new-readback-empty-inventory', False, [sys.executable, *mode,
                     str(H/'reproduce.py'), '--foundation', str(clone),
                     '--out', str(out/'not-created'), '--check']))

    def run(item):
        index, (name, accepted, command) = item
        child = subprocess.run(command, capture_output=True, text=True)
        tag = str(index)+'-'+name
        stdout, stderr = out/(tag+'.stdout'), out/(tag+'.stderr')
        stdout.write_text(child.stdout)
        stderr.write_text(child.stderr)
        need((child.returncode == 0) == accepted, 'unexpected actual CLI outcome:'+tag)
        if not accepted:
            need('nonempty actual prior dependency inventory' in child.stderr,
                 'rejection must exercise the intended completeness gate')
        return {'case': name, 'command': command, 'returncode': child.returncode,
                'expected_accept': accepted, 'stdout_sha256': sha(stdout),
                'stderr_sha256': sha(stderr)}

    with futures.ThreadPoolExecutor(max_workers=2) as executor:
        rows = list(executor.map(run, enumerate(jobs)))
    result = {'status': 'PASS_ACTUAL_DEPENDENCY_COMPLETENESS_CONTROLS_ALL3_MODES',
              'cases': len(rows), 'controller_sha256': sha(__file__),
              'new_validator_sha256': sha(H/'reproduce.py'),
              'prior_validator_sha256': sha(H.parent/'spectral_final/reproduce.py'),
              'original_basis_result_sha256': sha(args.basis/'RESULT.json'),
              'original_log_sha256': original_log_hash, 'rows': rows,
              'scope': 'The original actual study/logs are unchanged. An owned copy with '
                       'empty rehashed dependency evidence is accepted by the old readback '
                       'and rejected by the additive direct-import completeness gate. '
                       'No mathematical source/proof/object is changed.'}
    pending = out/'RESULT.pending.json'
    pending.write_text(json.dumps(result, indent=2)+'\n')
    os.replace(pending, out/'RESULT.json')
    print(result['status'])

if __name__ == '__main__':
    main()
