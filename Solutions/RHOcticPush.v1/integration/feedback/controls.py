#!/usr/bin/env python3
"""Run actual frozen734 acceptance CLI controls in normal/-O/-OO modes.

Only an explicitly owned regular-file copy is mutated. Each case preserves the
original accepted run, pins an expected rejection gate, and restores exact bytes.
Audit/dependency mutations are rehashed, so rejection cannot rely on stale hashes.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import math
import os
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def owned_bytes(root):
    return sum(p.stat().st_size for p in root.rglob('*')
               if p.is_file() and not p.is_symlink())


def dump(value):
    return (json.dumps(value, indent=2, allow_nan=False)+'\n').encode()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    run, out = args.run.resolve(), args.out.resolve()
    need(run.is_dir() and not run.is_symlink(), 'actual accepted run directory')
    need(not out.exists() and not out.is_relative_to(run)
         and not run.is_relative_to(out), 'fresh separate experiment-owned controls output')
    original_result = (run/'RESULT.json').read_bytes()
    original_result_sha = sha(run/'RESULT.json')
    need(json.loads(original_result)['status'] ==
         'PASS_FRESH_FEEDBACK11_FULL_FUNCTION_AND_CANONICAL_CONSUMERS', 'accepted734 run')
    out.mkdir(parents=True)
    clone = out/'mutant'
    shutil.copytree(run, clone, symlinks=True)
    result_original = (clone/'RESULT.json').read_bytes()
    build_original = (clone/'BUILD.json').read_bytes()
    manifest = json.loads((clone/'SOURCE_CLOSURE.executed.json').read_text())
    first = manifest['modules'][0]['module']
    relative = first.replace('.', '/')
    rows = []
    controller = HERE/'reproduce.py'
    started = time.monotonic()

    def cli(case, want, gate=None, target=clone):
        def invocation(mode):
            name = 'normal' if not mode else mode[0][1:]
            command = [sys.executable, *mode, str(controller), '--verify', str(target)]
            begin = time.monotonic()
            process = subprocess.run(command, capture_output=True, text=True)
            label = str(len(rows))+'-'+case+'-'+name
            stdout, stderr = out/(label+'.stdout'), out/(label+'.stderr')
            stdout.write_text(process.stdout)
            stderr.write_text(process.stderr)
            need((process.returncode == 0) is want, 'wrong actual outcome:'+label)
            if gate is not None:
                need(gate in process.stderr, 'wrong rejection gate:'+label)
            return {'case': case, 'mode': name, 'command': command,
                    'returncode': process.returncode, 'expected_accept': want,
                    'expected_gate': gate, 'seconds': time.monotonic()-begin,
                    'stdout': stdout.name, 'stderr': stderr.name,
                    'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)}
        # The three read-only invocations are independent and see fixed bytes.
        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            results = list(pool.map(invocation, [[], ['-O'], ['-OO']]))
        rows.extend(results)
        (out/'PROGRESS.json').write_bytes(dump({'completed_CLI_decisions': len(rows),
                                               'last_case': case}))

    def mutation(case, gate, change):
        changed = {}

        def replace(path, data):
            need(path.is_file() and not path.is_symlink()
                 and path.resolve().is_relative_to(clone), 'owned regular mutation target')
            if path not in changed:
                changed[path] = path.read_bytes()
            path.write_bytes(data)

        rr = json.loads(result_original)
        build = json.loads(build_original)
        try:
            change(rr, build, replace)
            if (clone/'BUILD.json').read_bytes() != build_original:
                rr['BUILD_sha256'] = sha(clone/'BUILD.json')
            # Receipt files are explicitly excluded from this existing gate.
            rr['owned_disk_before_result_bytes'] = (
                owned_bytes(clone)-(clone/'RESULT.json').stat().st_size)
            replace(clone/'RESULT.json', dump(rr))
            cli(case, False, gate)
        finally:
            for path, data in changed.items():
                path.write_bytes(data)
            need((clone/'RESULT.json').read_bytes() == result_original
                 and (clone/'BUILD.json').read_bytes() == build_original,
                 'exact mutated metadata restoration')

    def field(key, value):
        return lambda rr, build, replace: rr.__setitem__(key, value)

    def bytes_change(path):
        return lambda rr, build, replace: replace(path, path.read_bytes()+b'\nMUTATION\n')

    def audit_change(action):
        def apply(rr, build, replace):
            path = clone/'logs/FinalFeedbackAudit.stdout'
            text = action(path.read_text())
            replace(path, text.encode())
            build['modules'][-1]['stdout_sha256'] = sha(path)
            replace(clone/'BUILD.json', dump(build))
        return apply

    def change_audit_payload(text, prefix, action):
        lines = text.splitlines()
        for i, line in enumerate(lines):
            if line.startswith(prefix):
                value = json.loads(line[len(prefix):])
                changed = action(value)
                if changed is None:
                    continue
                lines[i] = prefix+json.dumps(changed, separators=(',', ':'))
                return '\n'.join(lines)+'\n'
        raise ValueError('No matching actual audit payload')

    def native_axiom(text):
        return change_audit_payload(text, 'RH_FEEDBACK_FINAL_THEOREM ',
                                   lambda x: dict(x, axioms=x['axioms']+['Lean.ofReduceBool']))

    def unused_parameter(text):
        def action(value):
            if not value['lambda_parameters']:
                return None
            value['lambda_parameters'][0]['used_in_body'] = False
            return value
        return change_audit_payload(text, 'RH_FEEDBACK_FINAL_BODY ', action)

    def duplicate_audit(text):
        prefix = 'RH_FEEDBACK_FINAL_THEOREM '
        lines = text.splitlines()
        for i, line in enumerate(lines):
            if line.startswith(prefix):
                value = json.loads(line[len(prefix):])
                payload = line[len(prefix):]
                lines[i] = prefix+'{"name":'+json.dumps(value['name'])+','+payload[1:]
                return '\n'.join(lines)+'\n'
        raise ValueError('No actual theorem audit')

    def dependency(action):
        def apply(rr, build, replace):
            probe = rr['dependency_probes'][0]
            path = clone/'dependencies'/probe['stdout']
            replace(path, action(path.read_text()).encode())
            probe['stdout_sha256'] = sha(path)
        return apply

    def omit_direct(text):
        suffix = '/'+manifest['modules'][0]['application_imports'][0].replace('.', '/')+'.olean'
        lines = text.splitlines()
        after = [line for line in lines if not line.endswith(suffix)]
        need(after and after != lines, 'remove actual declared import')
        return '\n'.join(after)+'\n'

    cases = [
        ('source-bytes', 'source/object association',
         bytes_change(clone/'source'/(relative+'.lean'))),
        ('object-bytes', 'source/object association',
         bytes_change(clone/'objects'/(relative+'.olean'))),
        ('stdout-bytes', 'compiler log', bytes_change(clone/'logs'/(first+'.stdout'))),
        ('controller-bytes', 'controller execution identity',
         bytes_change(clone/'reproduce.executed.py')),
        ('capture-bytes', 'registered source capture identity',
         bytes_change(clone/'SOURCE_CLOSURE.executed.json')),
        ('float-census', 'exact integer resource and census fields',
         field('fresh_scientific_modules', 10.0)),
        ('bool-census', 'exact integer resource and census fields',
         field('fresh_scientific_modules', True)),
        ('float-policy', 'exact resource policy', field('Lean_threads', 2.0)),
        ('bool-policy', 'exact resource policy', field('max_parallel_jobs', True)),
        ('wrong-schema', 'exact replay schema', field('schema', 'WRONG_SCHEMA')),
        ('negative-seconds', 'finite observed build/probe wall time', field('seconds', -1)),
        ('false-PV', 'trust categories', field('source_first_PV_claim', True)),
        ('false-cache', 'trust categories', field('historical_application_cache_used', True)),
        ('missing-probe', 'all11 import probes',
         lambda rr, build, replace: rr['dependency_probes'].pop()),
        ('empty-rehashed-deps', 'nonempty actual new dependency inventory', dependency(lambda _: '')),
        ('omitted-rehashed-direct-import', 'declared direct application import missing',
         dependency(omit_direct)),
        ('foreign-rehashed-dep', 'foreign or drifted application object',
         dependency(lambda t: t+'/tmp/foreign-application.olean\n')),
        ('native-rehashed-audit', 'nonstandard proof axiom or foreign theorem',
         audit_change(native_axiom)),
        ('unused-rehashed-proof-input', 'unused claimed final proof input',
         audit_change(unused_parameter)),
        ('duplicate-rehashed-audit-key', 'duplicate JSON audit key',
         audit_change(duplicate_audit)),
    ]
    (out/'PLAN.json').write_bytes(dump({'status': 'CONTROLS_PLAN_NOT_ACCEPTANCE',
        'expected_CLI_decisions': (len(cases)+3)*3,
        'cases': ['original-accepted', 'regular-relocated-copy']+
                 [x[0] for x in cases]+['restored'],
        'modes': ['normal', '-O', '-OO'], 'controller_sha256': sha(controller),
        'test_source_sha256': sha(__file__), 'accepted_RESULT_sha256': original_result_sha,
        'mutation_scope': 'Only owned clone; numerical and original accepted inputs preserved'}))
    cli('original-accepted', True, target=run)
    cli('regular-relocated-copy', True)
    for name, gate, change in cases:
        mutation(name, gate, change)
    cli('restored', True)
    need(len(rows) == (len(cases)+3)*3, 'all planned actual CLI decisions')
    need((run/'RESULT.json').read_bytes() == original_result, 'original result unchanged')
    for row in rows:
        need(sha(out/row['stdout']) == row['stdout_sha256']
             and sha(out/row['stderr']) == row['stderr_sha256'], 'actual decision logs')
    receipt = {'status': 'PASS_ACTUAL_FEEDBACK734_CLI_CONTROLS_ALL_MODES',
        'actual_CLI_decisions': len(rows), 'rows': rows,
        'controller_sha256': sha(controller), 'test_source_sha256': sha(__file__),
        'accepted_RESULT_sha256': original_result_sha,
        'seconds': time.monotonic()-started, 'original_accepted_run_unchanged': True,
        'source_first_PV_claim': False}
    pending = out/'CANDIDATE.json'
    pending.write_bytes(dump(receipt))
    os.replace(pending, out/'RESULT.json')
    print(receipt['status'], len(rows), flush=True)


if __name__ == '__main__':
    main()
