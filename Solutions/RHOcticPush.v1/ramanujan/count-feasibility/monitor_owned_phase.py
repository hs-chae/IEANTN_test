#!/usr/bin/env python3
"""Passive sampled resource evidence for one exact owned process identity.

Never launches or signals a mathematical worker. A separate GNU-time receipt
must provide exact wall/max-child metrics and the actual stage exit status.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import sys
import time

HERE = Path(__file__).resolve().parent
CONTROLLER_SHA = '299b7a6ec84049af35c18f6e0cff2515b9115d49fbdd8cf7d0917c4564d16838'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    pending = path.with_name('.'+path.name+'.pending')
    need(not pending.exists(), 'fresh atomic resource receipt')
    pending.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(pending, path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--pid', type=int, required=True)
    parser.add_argument('--start-ticks', required=True)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    need(args.pid > 1 and args.start_ticks.isdigit(), 'explicit actual process identity')
    run, out = args.run.resolve(), args.out.resolve()
    need(run.is_dir() and not out.exists() and out.parent.is_dir() and
         not out.is_relative_to(run), 'fresh separate owned measurement directory')
    source = HERE/'recover_count_v2.py'
    need(sha(source) == CONTROLLER_SHA, 'unchanged previously reviewed resource helper')
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(HERE))
    spec = importlib.util.spec_from_file_location('frozen_passive_resource_helper', source)
    controller = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = controller
    spec.loader.exec_module(controller)
    def current():
        identity = controller.process(args.pid)
        if identity is None or identity['start_ticks'] != args.start_ticks:
            return None
        try:
            state = Path('/proc', str(args.pid), 'stat').read_text().rsplit(')', 1)[1].split()[0]
        except FileNotFoundError:
            return None
        return None if state == 'Z' else identity

    def complete_forest(root):
        # Linux records children per calling thread. ThreadPoolExecutor's
        # Popen children are absent from task/<group-leader>/children.
        todo, seen, rows = [root], set(), []
        while todo:
            pid = todo.pop()
            if pid in seen:
                continue
            seen.add(pid)
            row = controller.process(pid, True)
            if row is None:
                continue
            rows.append(row)
            try:
                tasks = list(Path('/proc', str(pid), 'task').iterdir())
            except FileNotFoundError:
                continue
            for task in tasks:
                try:
                    todo.extend(int(child) for child in (task/'children').read_text().split())
                except FileNotFoundError:
                    continue
        return rows

    identity = current()
    need(identity is not None,
         'target process is genuinely live with exact start ticks')
    out.mkdir()
    (out/'monitor.executed.py').write_bytes(Path(__file__).read_bytes())
    save(out/'PLAN.json', dict(pid=args.pid, start_ticks=args.start_ticks, run=str(run),
        monitor_sha256=sha(__file__), frozen_helper_sha256=CONTROLLER_SHA,
        collector='ALL_THREAD_CHILDREN_V2',
        sample_interval_seconds=1, own_math_worker_launches=0, signals_sent=0,
        measurement='Sampled owned forest RSS/PSS and disk; not an exact peak or mathematical acceptance.'))
    peaks = dict(sampled_forest_RSS_bytes=0, sampled_forest_PSS_bytes=0,
                 observed_individual_VmHWM_bytes=0, observed_individual_VmPeak_bytes=0,
                 observed_owned_disk_bytes=controller.disk(run))
    samples, start, last_disk = 0, time.monotonic(), 0.0
    error = None
    try:
        with (out/'SAMPLES.jsonl').open('w') as stream:
            while True:
                identity = current()
                if identity is None:
                    break
                now = time.monotonic()
                rows = complete_forest(args.pid)
                if not rows:
                    need(current() is None, 'live observed root must have a nonempty resource forest')
                    break
                rss = sum(row.get('VmRSS', 0) for row in rows)
                pss = sum(row.get('Pss', 0) for row in rows)
                peaks['sampled_forest_RSS_bytes'] = max(peaks['sampled_forest_RSS_bytes'], rss)
                peaks['sampled_forest_PSS_bytes'] = max(peaks['sampled_forest_PSS_bytes'], pss)
                for key, field in [('observed_individual_VmHWM_bytes', 'VmHWM'),
                                   ('observed_individual_VmPeak_bytes', 'VmPeak')]:
                    peaks[key] = max([peaks[key]]+[row.get(field, 0) for row in rows])
                if now-last_disk >= 5:
                    peaks['observed_owned_disk_bytes'] = max(peaks['observed_owned_disk_bytes'],
                                                            controller.disk(run))
                    last_disk = now
                stream.write(json.dumps(dict(unix=time.time(), elapsed_seconds=now-start,
                    actual_MemAvailable_bytes=controller.available(), forest_RSS_bytes=rss,
                    forest_PSS_bytes=pss, processes=rows), allow_nan=False)+'\n')
                stream.flush()
                samples += 1
                time.sleep(1)
    except BaseException as caught:
        error = repr(caught)
        raise
    finally:
        peaks['observed_owned_disk_bytes'] = max(peaks['observed_owned_disk_bytes'], controller.disk(run))
        save(out/'METRICS.json', dict(status='ROOT_EXIT_OBSERVED_RESOURCE_SAMPLES_ONLY' if error is None
             else 'RESOURCE_MONITOR_FAILED_PARTIAL_SAMPLES', error=error,
             plan_sha256=sha(out/'PLAN.json'), samples_sha256=sha(out/'SAMPLES.jsonl'),
             samples=samples, observed_seconds=time.monotonic()-start, peaks=peaks,
             exact_max_child_RSS_or_whole_run_wall_claim=False,
             mathematical_acceptance_claim=False, worker_exit_code_or_OOM_attribution=None,
             trust='Linux process/proportional-memory accounting; one-second observations may miss peaks. '
                   'Consult separate GNU-time, actual exit receipts and mathematical validators.'))
    print('PASSIVE_RESOURCE_SAMPLES_COMPLETE', samples)


if __name__ == '__main__':
    main()
