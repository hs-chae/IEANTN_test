#!/usr/bin/env python3
"""Eighteen actual source-prefix CLI decisions, preserving the failed original."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, shutil, subprocess, sys, time

HERE = Path(__file__).resolve().parent


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--basis', type=Path, required=True)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source_pins = {name: sha(HERE/name) for name in
                   ['test_prefix.py', 'check_prefix.py', 'reproduce.py', 'resume_prefix.py']}
    run, out = args.run.resolve(), args.out.resolve()
    need(not out.exists() and not out.is_relative_to(run)
         and not out.is_relative_to(args.basis.resolve()), 'fresh separate owned control directory')
    out.mkdir(parents=True)
    clone = out/'mutant'
    shutil.copytree(run, clone, symlinks=True,
                    ignore=lambda directory, names: ['foundation'] if Path(directory) == run else [])
    originals = {path.relative_to(run).as_posix(): sha(path)
        for path in run.rglob('*') if path.is_file() and not path.is_symlink()
        and not path.is_relative_to(run/'foundation')}
    build = json.loads((run/'BUILD.json').read_text())
    source_name = 'source/'+build['modules'][0]['module'].replace('.', '/')+'.lean'
    changed = ['FAILURE.json', 'RESOURCE_ADMISSION.json', 'BUILD.json', source_name]
    original_bytes = {relative: (run/relative).read_bytes() for relative in changed}
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    environment['IEANTN_GENERIC_CONTEXT'] = str(args.context.resolve())
    environment.pop('PYTHONOPTIMIZE', None)
    modes, rows = [[], ['-O'], ['-OO']], []
    started = time.monotonic()
    cases = [('original-positive', None),
        ('boolean-completed-count', 'precise missing-runtime stage and114 completed modules'),
        ('wrong-memory-cap', 'exact original64GiB source lane and512GiB host reserve'),
        ('changed-proof-source', 'exact prefix source/object hashes'),
        ('boolean-child-RSS', 'actual finite prefix resource measurements'),
        ('invented-compiler-duration', 'prefix compiler duration against actual GNU time')]
    for name, gate in cases:
        for relative, data in original_bytes.items():
            (clone/relative).write_bytes(data)
        if name == 'boolean-completed-count':
            path = clone/'FAILURE.json'
            value = json.loads(path.read_text()); value['completed_modules'] = False
            path.write_text(json.dumps(value)+'\n')
        elif name == 'wrong-memory-cap':
            path = clone/'RESOURCE_ADMISSION.json'
            value = json.loads(path.read_text()); value['memory_cap_bytes'] = 4*(1 << 30)
            path.write_text(json.dumps(value)+'\n')
        elif name == 'changed-proof-source':
            (clone/source_name).write_bytes(original_bytes[source_name]+b'\n')
        elif name in ['boolean-child-RSS', 'invented-compiler-duration']:
            value = json.loads(original_bytes['BUILD.json'])
            value['modules'][0]['peak_RSS_KiB' if name == 'boolean-child-RSS' else 'seconds'] = (
                False if name == 'boolean-child-RSS' else value['modules'][0]['seconds']+1000)
            (clone/'BUILD.json').write_text(json.dumps(value)+'\n')
        def trial(index):
            mode = modes[index]
            label = name+'-O'+str(index)
            receipt = out/(label+'.prefix.json')
            command = [sys.executable, '-B', *mode, str(HERE/'check_prefix.py'),
                '--run', str(run if gate is None else clone), '--basis', str(args.basis.resolve()),
                '--out', str(receipt)]
            process = subprocess.run(command, env=environment, capture_output=True, text=True)
            (out/(label+'.stdout')).write_text(process.stdout)
            (out/(label+'.stderr')).write_text(process.stderr)
            need((process.returncode == 0) is (gate is None), 'actual prefix CLI decision:'+label)
            if gate is None:
                accepted = json.loads(receipt.read_text())
                need(accepted['prefix']['prefix_count'] == 114
                     and accepted['python_optimization'] == index
                     and accepted['native_outputs_reused'] is False, 'actual positive prefix receipt')
            else:
                need(gate in process.stderr and not receipt.exists(), 'specific actual rejection gate:'+label)
            return {'case': name, 'mode': mode, 'command': command,
                'returncode': process.returncode, 'expected_accept': gate is None, 'expected_gate': gate,
                'stdout': label+'.stdout', 'stderr': label+'.stderr',
                'stdout_sha256': sha(out/(label+'.stdout')),
                'stderr_sha256': sha(out/(label+'.stderr')),
                'accepted_prefix_receipt_sha256': sha(receipt) if gate is None else None}
        with ThreadPoolExecutor(max_workers=3) as pool:
            rows.extend(pool.map(trial, range(3)))
        (out/'PROGRESS.json').write_text(json.dumps({'completed': len(rows), 'last': name})+'\n')
    for relative, data in original_bytes.items():
        (clone/relative).write_bytes(data)
    need(all(sha(run/relative) == value for relative, value in originals.items()),
         'original failed run evidence unchanged')
    need(len(rows) == 18 and len({row['stdout'] for row in rows})
         == len({row['stderr'] for row in rows}) == 18, 'all18 commands and36 distinct raw logs')
    for row in rows:
        for suffix in ['stdout', 'stderr']:
            need(sha(out/row[suffix]) == row[suffix+'_sha256'], 'actual control raw log binding')
    need(all(sha(HERE/name) == value for name, value in source_pins.items()),
         'all executed prefix test and checker sources unchanged')
    result = {'status': 'PASS_ALL18_ACTUAL_PREFIX_CLI_CONTROLS_NORMAL_O_OO',
        'test_source_sha256': source_pins['test_prefix.py'], 'CLI_source_sha256': source_pins['check_prefix.py'],
        'engine_source_sha256': source_pins['reproduce.py'],
        'helper_source_sha256': source_pins['resume_prefix.py'],
        'generic_context_sha256': sha(args.context), 'rows': rows,
        'seconds': time.monotonic()-started, 'original_failed_run_unchanged': True,
        'scope': 'Three original-prefix admissions and15 intended rejection gates; mutants are owned '
            'clones excluding foundation. No rejected run or native output is promoted.'}
    pending = out/'.RESULT.pending.json'
    pending.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    os.replace(pending, out/'RESULT.json')
    print(result['status'])


if __name__ == '__main__':
    main()
