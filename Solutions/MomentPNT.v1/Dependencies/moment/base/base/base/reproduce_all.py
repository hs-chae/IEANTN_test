"""Reproduce the full locked3942-source graph from public generic dependencies."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
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
    parser.add_argument('--prior-jobs', type=int, default=14)
    parser.add_argument('--frame-jobs', type=int, default=14)
    parser.add_argument('--weight-jobs', type=int, default=6)
    parser.add_argument('--jobs', type=int, default=14)
    parser.add_argument('--edge-jobs', type=int, default=14)
    parser.add_argument('--cell-jobs', type=int, default=12)
    args = parser.parse_args()
    need(args.environment.is_file(), 'pinned public generic environment required')
    need(1 <= args.base_jobs <= 8 and 1 <= args.prior_jobs <= 16
         and 1 <= args.frame_jobs <= args.prior_jobs and 1 <= args.weight_jobs <= args.prior_jobs
         and 1 <= args.jobs <= 16 and 1 <= args.edge_jobs <= args.jobs
         and 1 <= args.cell_jobs <= args.jobs, 'bounded explicit worker counts')
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh output outside capsule')
    out.mkdir(parents=True)
    start = time.monotonic()
    flags = ['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else []
    steps = []
    def run(name, command):
        began = time.monotonic()
        with (out / (name + '.stdout')).open('wb') as stdout, (out / (name + '.stderr')).open('wb') as stderr:
            q = subprocess.run(command, stdout=stdout, stderr=stderr)
        need(q.returncode == 0, 'failed: ' + name + '; partial evidence preserved')
        steps.append(dict(name=name, command=command, seconds=time.monotonic() - began))
    run('unchanged-base-and-corrected-frame-weight-pipeline', [sys.executable, *flags,
        str(B / 'base/reproduce_all.py'), '--environment', str(args.environment.resolve()),
        '--out', str(out / 'base-run'), '--base-jobs', str(args.base_jobs),
        '--jobs', str(args.prior_jobs), '--frame-jobs', str(args.frame_jobs),
        '--weight-jobs', str(args.weight_jobs)])
    run('complete-main-source-extension', [sys.executable, *flags, str(B / 'reproduce.py'),
        '--environment', str(args.environment.resolve()), '--prior-run', str(out / 'base-run'),
        '--out', str(out / 'complete-main-run'), '--jobs', str(args.jobs),
        '--edge-jobs', str(args.edge_jobs), '--cell-jobs', str(args.cell_jobs)])
    receipt_path = out / 'complete-main-run/RECEIPT.json'
    receipt = json.loads(receipt_path.read_text())
    need(receipt['status'] == 'PASS_SOURCE_COLD_COMPLETE_MODELED_MAIN_OBSERVED_OUTPUT_ANT'
         and receipt['source_modules'] == 3942 and receipt['selected_theorem_roots'] == 11976
         and receipt['outside_application_object_inputs'] == []
         and receipt['completed_fresh_source_graph'] is True, 'complete actual selected graph acceptance')
    result = dict(status='PASS_CLEAN_3942_SOURCE_MAIN_OBSERVED_OUTPUT_ANT_REPRODUCTION',
        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), complete_receipt_sha256=sha(receipt_path),
        elapsed_seconds=time.monotonic() - start, steps=steps, namespace_isolated=False,
        universal_host_IO_success=False,
        qualification='Complete fixed source graph from only public generic inputs. Actual application source/execution/math and fresh final128byte observation are linked; compiler/runtime/ABI/OS/hardware contracts remain explicit. Final namespace isolation and original68-function migration are separate.')
    temp = out / 'RECEIPT.pending'
    temp.write_text(json.dumps(result, indent=2) + '\n')
    temp.replace(out / 'RECEIPT.json')
    print(json.dumps({k: v for k, v in result.items() if k != 'steps'}))

if __name__ == '__main__':
    main()
