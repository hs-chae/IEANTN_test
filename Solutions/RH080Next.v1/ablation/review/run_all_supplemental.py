#!/usr/bin/env python3
"""Replay all13 exact censored locks offline, with fresh outputs and no pilot reuse.

Historical executions and primary statuses remain immutable. The final strict
validator is the acceptance gate; worker exit status alone is insufficient.
"""
import argparse, concurrent.futures, json, shutil, subprocess, sys, time
from pathlib import Path
import run_review as common
import run_supplemental as worker


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--prepare-only', action='store_true')
    args = ap.parse_args()
    common.need(1 <= args.workers <= 4, 'Workers must be between1 and4')
    common.need(args.out.resolve().is_relative_to(worker.ROOT) and not args.out.exists(),
                'Fresh owned supplemental batch path required')
    plan = common.load(common.D / 'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json')
    rows = plan['rows']
    common.need(len(rows) == len({r['trial'] for r in rows}) == 13,
                'Exact13 censored population required')
    common.need(common.sha(worker.RUNTIME) == worker.RUNTIME_SHA,
                'Original richest commonD runtime differs')
    memory = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines()
                      if line.startswith('MemAvailable:'))) * 1024
    common.need(memory >= (256 + args.workers * 64) * 2**30,
                'Host reserve plus offline worker memory unavailable')
    ancestor = args.out.parent
    while not ancestor.exists():
        ancestor = ancestor.parent
    free_disk = shutil.disk_usage(ancestor).free
    common.need(free_disk >= 2**40, 'Independent1TiBfree disk required')
    args.out.mkdir(parents=True)
    (args.out / 'runs').mkdir()
    commands = [dict(trial=row['trial'], out=str(args.out / 'runs' / row['trial']),
                     command=[sys.executable, str(Path(worker.__file__)), '--trial', row['trial'],
                              '--out', str(args.out / 'runs' / row['trial'])]) for row in rows]
    frozen = dict(status='FROZEN_ALL13_SUPPLEMENTAL_POSTHOC_PLAN', primary_eligible=False,
                  primary_results_changed=False, external_model_inference_calls=0,
                  universe=[r['trial'] for r in rows], same_original_common_runtime=str(worker.RUNTIME),
                  runtime_sha256=worker.RUNTIME_SHA, controller_sha256=common.sha(Path(worker.__file__)),
                  coordinator_sha256=common.sha(Path(__file__)), workers=args.workers,
                  memory_gib_each=64, scratch_gib_each=12, cpus_each=4,
                  MemAvailable_bytes=memory, free_disk_bytes=free_disk,
                  wall_seconds_each=1200, no_historical_pilot_reuse=True, rows=commands)
    common.save(args.out / 'PLAN.json', frozen)
    (args.out / 'coordinator.executed.py').write_bytes(Path(__file__).read_bytes())
    (args.out / 'worker.executed.py').write_bytes(Path(worker.__file__).read_bytes())
    if args.prepare_only:
        print('PREPARED_ONLY: no worker executed and no acceptance claimed')
        return

    def execute(row):
        started = time.monotonic()
        with (args.out / (row['trial'] + '.stdout')).open('xb') as stdout, \
             (args.out / (row['trial'] + '.stderr')).open('xb') as stderr:
            result = subprocess.run(row['command'], stdout=stdout, stderr=stderr)
        return dict(row, returncode=result.returncode, seconds=time.monotonic()-started)

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for future in concurrent.futures.as_completed([pool.submit(execute, row) for row in commands]):
            row = future.result()
            results.append(row)
            print(row['trial'], row['returncode'], flush=True)
            pending = args.out / 'PROGRESS.pending'
            pending.write_text(json.dumps(dict(completed=len(results), total=13, rows=results), indent=2)+'\n')
            pending.replace(args.out / 'PROGRESS.json')
    common.save(args.out / 'RUNS.json', dict(rows=results))
    common.need(all(row['returncode'] == 0 for row in results),
                'Supplemental worker failed; partial outputs retained without acceptance')
    command = [sys.executable, str(Path(__file__).with_name('check_supplemental.py')),
               '--runs', str(args.out / 'RUNS.json'), '--output', str(args.out / 'ACCEPTED.json')]
    checked = subprocess.run(command, capture_output=True, text=True)
    (args.out / 'validation.stdout').write_text(checked.stdout)
    (args.out / 'validation.stderr').write_text(checked.stderr)
    common.need(checked.returncode == 0 and (args.out / 'ACCEPTED.json').is_file(),
                'Actual complete13 validator rejected; partial outputs retained')
    common.save(args.out / 'RESULT.json', dict(status='ALL13_EXACT_LOCK_SUPPLEMENTAL_REPLAY_AND_VALIDATION_PASS',
                rows=results, acceptance_sha256=common.sha(args.out / 'ACCEPTED.json'),
                primary_eligible=False, primary_results_changed=False, external_model_inference_calls=0))


if __name__ == '__main__':
    main()
