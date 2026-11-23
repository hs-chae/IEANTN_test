#!/usr/bin/env python3
"""Run the parallel RHLimit replay with separate process/group resource limits.

The launcher sets an address-space limit inherited by its child tree. The inner
C-log replay sets tighter 16/48 GiB compiler limits. This does not alter any source.
"""
from pathlib import Path
import argparse, hashlib, json, os, resource, signal, subprocess, time, shutil

def need(ok, message):
    if not ok:
        raise ValueError(message)

def available():
    return int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().split('\n')
                    if line.startswith('MemAvailable:'))) * 1024

def processes():
    result = {}
    for p in Path('/proc').iterdir():
        if p.name.isdigit():
            try:
                raw = (p / 'stat').read_text()
                fields = raw[raw.rfind(')') + 2:].split()
                result[int(p.name)] = {'ppid': int(fields[1]), 'start_ticks': int(fields[19]),
                                      'rss_bytes': int(fields[21]) * os.sysconf('SC_PAGE_SIZE')}
            except (OSError, ValueError, IndexError):
                pass
    return result

def descendants(table, parent):
    own = {parent}
    while True:
        more = {pid for pid, v in table.items() if v['ppid'] in own}
        if more <= own:
            return own
        own |= more

def atomic(path, data):
    temp = path.with_suffix('.pending')
    temp.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')
    os.replace(temp, path)

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--limit-gib', type=int, default=80)
    p.add_argument('--wall-seconds', type=int, default=10800)
    p.add_argument('--group-gib', type=int, default=240)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args(); cmd = a.command
    if cmd and cmd[0] == '--':
        cmd = cmd[1:]
    need(cmd and not a.record.exists(), 'command and fresh record required')
    need(1 <= a.limit_gib <= 80 and 1 <= a.group_gib <= 240 and 1 <= a.wall_seconds <= 14400, 'resource policy bounds')
    limit = a.limit_gib * 1024**3; group = a.group_gib * 1024**3; reserve = 512 * 1024**3
    initial = available(); need(initial >= reserve + group, 'host reserve plus job limit unavailable')
    a.record.mkdir(parents=True)
    start = time.monotonic()
    def admission():
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    with (a.record / 'stdout.txt').open('w') as stdout, (a.record / 'stderr.txt').open('w') as stderr:
        child = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, preexec_fn=admission,
                                 start_new_session=True)
        table = processes(); identity = table.get(child.pid)
        row = {'schema': 'BOUNDED_RELOCATED_SOURCE_REPLAY_V1', 'status': 'RUNNING',
               'command': cmd, 'controller_pid': os.getpid(), 'child_pid': child.pid,
               'child_start_ticks': identity['start_ticks'] if identity else None,
               'per_process_address_limit_bytes': limit, 'host_reserve_bytes': reserve,
               'aggregate_new_study_limit_bytes': group,
               'controller_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'initial_free_disk_bytes': shutil.disk_usage(a.record.parent).free,
               'initial_host_available_bytes': initial, 'maximum_sampled_tree_RSS_bytes': 0,
               'minimum_host_available_bytes': initial, 'sample_interval_seconds': 2,
               'wall_limit_seconds': a.wall_seconds,
               'limit_scope': 'Inherited per-process RLIMIT_AS, sampled owned process-tree RSS watchdog; no host/security changes',
               'actual_OOM_events': None, 'OOM_evidence': 'No cgroup memory.events access boundary; signal/status and process resources are reported separately. Do not infer kernel OOM count from successful exit.'}
        atomic(a.record / 'LAUNCH.json', row)
        with (a.record / 'samples.jsonl').open('w') as samples:
            while child.poll() is None:
                table = processes(); own = descendants(table, child.pid)
                rss = sum(table[pid]['rss_bytes'] for pid in own if pid in table)
                avail = available(); elapsed = time.monotonic() - start
                row['maximum_sampled_tree_RSS_bytes'] = max(row['maximum_sampled_tree_RSS_bytes'], rss)
                row['minimum_host_available_bytes'] = min(row['minimum_host_available_bytes'], avail)
                samples.write(json.dumps({'elapsed_seconds': elapsed, 'tree_RSS_bytes': rss,
                                          'host_available_bytes': avail, 'owned_processes': len(own)}) + '\n')
                samples.flush()
                reason = ('wall limit' if elapsed > a.wall_seconds else
                          'host reserve' if avail < reserve else
                          'owned process-tree RSS group cap' if rss > group else None)
                if reason:
                    row['watchdog_stop_reason'] = reason
                    os.killpg(child.pid, signal.SIGTERM)
                    try:
                        child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                    break
                time.sleep(2)
        row['returncode'] = child.wait(); row['elapsed_seconds'] = time.monotonic() - start
        row['controller_unchanged'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == row['controller_sha256']
        need(row['controller_unchanged'], 'resource controller changed during run')
        row['status'] = 'PASS_PROCESS_EXIT_ZERO' if row['returncode'] == 0 else 'FAILED_PROCESS_EXIT'
        row['stdout_sha256'] = hashlib.sha256((a.record / 'stdout.txt').read_bytes()).hexdigest()
        row['stderr_sha256'] = hashlib.sha256((a.record / 'stderr.txt').read_bytes()).hexdigest()
        atomic(a.record / 'RESULT.json', row)
        print(json.dumps({key: row[key] for key in ['status', 'returncode', 'elapsed_seconds',
                                                   'maximum_sampled_tree_RSS_bytes']}))
        raise SystemExit(0 if row['returncode'] == 0 else 1)

if __name__ == '__main__':
    main()
