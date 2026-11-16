"""Reproduce raw C, numerical regeneration, base1412 and the actual-weight append."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import shutil
import sys
import time

B = Path(__file__).resolve().parent

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--environment', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--base-jobs', type=int, default=8)
    parser.add_argument('--jobs', type=int, default=14)
    parser.add_argument('--frame-jobs', type=int, default=14)
    parser.add_argument('--weight-jobs', type=int, default=6)
    args = parser.parse_args()
    need(args.environment.is_file(), 'public pinned environment required')
    need(1 <= args.base_jobs <= 8 and 1 <= args.jobs <= 16
         and 1 <= args.frame_jobs <= args.jobs and 1 <= args.weight_jobs <= args.jobs,
         'bounded explicit phase job counts')
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh output outside capsule')
    out.mkdir(parents=True)
    from reproduce_append import BASE_VALIDATORS
    base_pins = dict(status='PINNED_BEFORE_CLEAN_BASE_PIPELINE', files=[
        dict(path=path, sha256=sha(B / 'base' / path), bytes=(B / 'base' / path).stat().st_size)
        for path in BASE_VALIDATORS])
    pin_path = out / 'BASE_VALIDATOR_PINS.json'
    pin_path.write_text(json.dumps(base_pins, indent=2) + '\n')
    start = time.monotonic()
    flags = ['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else []
    steps = []
    def run(name, command):
        began = time.monotonic()
        with (out / (name + '.stdout')).open('wb') as stdout, (out / (name + '.stderr')).open('wb') as stderr:
            q = subprocess.run(command, stdout=stdout, stderr=stderr)
        need(q.returncode == 0, 'failed ' + name + '; partial evidence preserved')
        steps.append(dict(name=name, command=command, seconds=time.monotonic() - began))
    run('unchanged-base-pipeline', [sys.executable, *flags, str(B / 'base/reproduce_all.py'),
        '--environment', str(args.environment.resolve()), '--out', str(out / 'base-run'),
        '--jobs', str(args.base_jobs), '--point-jobs', str(args.base_jobs)])
    shutil.copyfile(pin_path, out / 'base-run/VALIDATOR_PINS_V1.json')
    run('actual-frame-weight-append', [sys.executable, *flags, str(B / 'reproduce_append.py'),
        '--environment', str(args.environment.resolve()), '--base-run', str(out / 'base-run'),
        '--out', str(out / 'append-run'), '--jobs', str(args.jobs),
        '--frame-jobs', str(args.frame_jobs), '--weight-jobs', str(args.weight_jobs)])
    receipt = json.loads((out / 'append-run/RECEIPT.json').read_text())
    need(receipt['status'] == 'PASS_SOURCE_COLD_APPEND_ACTUAL_FRAMES_WEIGHTS_ANT'
         and receipt['outside_application_object_inputs'] == []
         and receipt['combined_fresh_replay_completed'] is True, 'complete appended proof acceptance')
    result = dict(status='PASS_COMPLETE_BASE_PLUS_ACTUAL_FRAME_WEIGHT_ANT_REPRODUCTION',
        elapsed_seconds=time.monotonic() - start, steps=steps,
        append_receipt_sha256=sha(out / 'append-run/RECEIPT.json'),
        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), full_program_source_first_PV=False,
        qualification='Complete fixed finite source-point/actual-weight conditional ANT graph; complete main, startup, stream/flush and final isolated execution remain separate.')
    temp = out / 'RECEIPT.pending'
    temp.write_text(json.dumps(result, indent=2) + '\n')
    temp.replace(out / 'RECEIPT.json')
    print(json.dumps({k: v for k, v in result.items() if k != 'steps'}))

if __name__ == '__main__':
    main()
