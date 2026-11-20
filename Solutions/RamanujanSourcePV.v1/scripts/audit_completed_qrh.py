#!/usr/bin/env python3
"""Audit the selected QRH proof terms after a successful fresh closure build.

This does not run or certify a C program. It rechecks source/object identities,
compiles a separate Lean dependency audit against only the fresh application
objects, and accepts only the ordinary three Lean mathematical axioms.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

S = Path(__file__).resolve().parents[1]
EXPECTED = {
    'CH2QRH.density_transfer_proved',
    'QRHPhase2.pi_expansion_phase2',
    'RamanujanPV.QRHClosure.pi144',
    'RamanujanPV.QRHFullTail.pi_two_sided_144',
}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cpu', type=int, default=8)
    args = parser.parse_args()
    build = args.build.resolve()
    out = args.out.resolve()
    need(not out.exists(), 'fresh owned audit output required')
    need(args.cpu in os.sched_getaffinity(0), 'audit CPU is unavailable')
    context_path = S / 'BUILD_CONTEXT.json'
    context = read(context_path)
    compiler = Path(context['compiler'])
    need(sha(compiler) == context['compiler_sha256'], 'Lean compiler identity')
    plan = read(build / 'PLAN.json')
    result = read(build / 'RESULT.json')
    need(result['status'] == 'FRESH_QRH_CLOSURE_BUILD_PASS', 'fresh closure is incomplete')
    need(result['old_application_objects_used'] is False, 'old application object policy')
    need(plan['old_application_objects_used'] is False, 'old application object plan')
    need(sha(context_path) == plan['context_sha256'], 'build context changed')
    rows = result['records']
    need(type(rows) is list and len(rows) == plan['module_count'], 'complete closure receipts')
    planned = {row['module']: row for row in plan['ordered_modules']}
    need(len(planned) == plan['module_count'], 'unique planned module identities')
    seen = set()
    peak_kib = []
    for row in rows:
        module = row['module']
        need(module in planned and module not in seen, 'unexpected/duplicate module')
        seen.add(module)
        need(type(row['exit_code']) is int and row['exit_code'] == 0, 'nonzero module exit')
        expected = planned[module]
        need(row['source'] == expected['source'], 'module source identity')
        need(row['source_sha256'] == expected['source_sha256'], 'planned source hash')
        need(sha(row['source']) == row['source_sha256'], 'changed current source ' + module)
        directory = build / 'audit' / module
        need(sha(directory / 'source.lean') == row['source_sha256'], 'source snapshot')
        for name in ['stdout', 'stderr', 'rusage']:
            need(sha(directory / name) == row[name + '_sha256'], 'changed module receipt')
        obj = build / 'lean' / Path(*module.split('.')).with_suffix('.olean')
        need(sha(obj) == row['object_sha256'], 'fresh object identity')
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)',
                          (directory / 'rusage').read_text())
        need(match is not None, 'missing actual peak RSS')
        peak_kib.append(int(match.group(1)))
    need(seen == set(planned), 'missing module')
    generic = []
    for dependency in context['generic_dependencies']:
        if not dependency['library_present']:
            continue
        root = Path(dependency['path'])
        need(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root,
             text=True).strip() == dependency['revision'], 'generic dependency revision')
        need(not subprocess.check_output(['git', 'status', '--porcelain',
             '--untracked-files=no'], cwd=root, text=True), 'changed generic tracked sources')
        generic.append(dependency['library'])
    need(generic == plan['generic_libraries'], 'generic library resolution')
    source = S / 'RamanujanPV' / 'QRHClosureAudit.lean'
    source_hash = sha(source)
    out.mkdir(parents=True)
    (out / 'source.lean').write_bytes(source.read_bytes())
    added_objects = out / 'lean'
    adapter_object = added_objects / 'RamanujanPV' / 'QRHFullTail.olean'
    # Lean selects a namespace directory as one import root. It does not merge
    # an incomplete RamanujanPV directory with a later LEAN_PATH directory.
    # Copy only these already hash-checked fresh objects into the added prefix.
    shutil.copytree(build / 'lean' / 'RamanujanPV', adapter_object.parent)
    obj = added_objects / 'RamanujanPV' / 'QRHClosureAudit.olean'
    environment = dict(os.environ, LEAN_PATH=os.pathsep.join(
        [str(added_objects), str(build / 'lean'), *generic]))
    adapter = S / 'RamanujanPV' / 'QRHFullTail.lean'
    adapter_hash = sha(adapter)
    adapter_directory = out / 'full-adapter'
    adapter_directory.mkdir()
    (adapter_directory / 'source.lean').write_bytes(adapter.read_bytes())
    adapter_command = ['/usr/bin/time', '-v', '-o', str(adapter_directory / 'rusage'),
                       '/usr/bin/prlimit', '--as=' + str(48 << 30), '--',
                       '/usr/bin/taskset', '-c', str(args.cpu), str(compiler), '-j1',
                       '-R', str(S), str(adapter), '-o', str(adapter_object)]
    adapter_started = time.monotonic()
    with (adapter_directory / 'stdout').open('wb') as stdout, (adapter_directory / 'stderr').open('wb') as stderr:
        adapter_run = subprocess.run(adapter_command, cwd=S, env=environment,
                                     stdout=stdout, stderr=stderr, check=False)
    adapter_receipt = {'exit_code': adapter_run.returncode, 'command': adapter_command,
                       'source_sha256': adapter_hash,
                       'elapsed_seconds': time.monotonic() - adapter_started,
                       'stdout_sha256': sha(adapter_directory / 'stdout'),
                       'stderr_sha256': sha(adapter_directory / 'stderr'),
                       'rusage_sha256': sha(adapter_directory / 'rusage')}
    atomic(adapter_directory / 'RUN.json', adapter_receipt)
    need(adapter_run.returncode == 0, 'full v6 adapter compile failed; attempt preserved')
    need(sha(adapter) == adapter_hash, 'adapter source changed during compile')
    adapter_receipt['object_sha256'] = sha(adapter_object)
    atomic(adapter_directory / 'RUN.json', adapter_receipt)
    command = [str(compiler), '-j1', '-R', str(S), str(source), '-o', str(obj)]
    full = ['/usr/bin/time', '-v', '-o', str(out / 'rusage'),
            '/usr/bin/prlimit', '--as=' + str(48 << 30), '--',
            '/usr/bin/taskset', '-c', str(args.cpu), *command]
    started = time.monotonic()
    with (out / 'stdout').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
        completed = subprocess.run(full, cwd=S, env=environment, stdout=stdout,
                                   stderr=stderr, check=False)
    receipt = {
        'status': 'AUDIT_EXECUTED_NOT_YET_ACCEPTED', 'exit_code': completed.returncode,
        'elapsed_seconds': time.monotonic() - started, 'command': full,
        'source': str(source), 'source_sha256': source_hash,
        'compiler_sha256': context['compiler_sha256'],
        'build_plan_sha256': sha(build / 'PLAN.json'),
        'build_result_sha256': sha(build / 'RESULT.json'),
        'closure_module_count': len(rows),
        'full_v6_adapter': adapter_receipt,
        'additional_application_object_root': str(added_objects),
        'closure_max_individual_peak_rss_bytes': max(peak_kib) * 1024,
        'old_application_objects_used': False,
        'native_source_text_scan_is_theorem_dependency_evidence': False,
        'source_first_program_verification_claim': False,
        'stdout_sha256': sha(out / 'stdout'),
        'stderr_sha256': sha(out / 'stderr'), 'rusage_sha256': sha(out / 'rusage'),
    }
    atomic(out / 'RUN.json', receipt)
    need(completed.returncode == 0, 'Lean axiom audit failed; attempt preserved')
    need(sha(source) == source_hash, 'audit source changed during compilation')
    output = (out / 'stdout').read_text()
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    need(len(matches) == len(EXPECTED), 'missing/extra actual axiom audit output')
    axioms = {}
    for theorem, values in matches:
        need(theorem in EXPECTED and theorem not in axioms, 'unexpected/duplicate theorem audit')
        names = {value.strip() for value in values.split(',') if value.strip()}
        need(names <= STANDARD, 'nonstandard/native/sorry axiom in ' + theorem)
        axioms[theorem] = sorted(names)
    need(set(axioms) == EXPECTED, 'missing selected theorem')
    receipt.update({
        'status': 'PASS_FRESH_QRH_SELECTED_THEOREM_AXIOM_AUDIT',
        'axioms': axioms, 'object_sha256': sha(obj),
        'remaining_trust': ['explicit sixteen literature hypotheses',
                            'generic pinned Lean kernel and dependencies',
                            'compiler/runtime/OS/hardware execution of the checker'],
    })
    atomic(out / 'RESULT.json', receipt)
    print(json.dumps({'status': receipt['status'], 'axioms': axioms,
                      'closure_module_count': len(rows)}))


if __name__ == '__main__':
    main()
