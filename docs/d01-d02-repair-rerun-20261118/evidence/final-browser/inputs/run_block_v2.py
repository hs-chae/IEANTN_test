# Copyright (c) 2026 IEANTN contributors. Apache-2.0.
"""Launch one reviewed balanced three-arm block with existing native authentication only.

No inference is possible without the separately created root-review start file.
Resource failures, budget exhaustion and mathematical review remain separate.
"""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

STUDY = Path(__file__).resolve().parents[1]
GiB = 1024 ** 3
CPU_SLOTS = [list(range(32, 40)), list(range(40, 48)), list(range(48, 56))]
stop_requested = False

def need(value, message):
    if not value:
        raise ValueError(message)

def load(path):
    def unique(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for block in iter(lambda: handle.read(1024 ** 2), b''):
            digest.update(block)
    return digest.hexdigest()

def pin(row):
    path = Path(row['path']).resolve()
    need(path.is_file() and not path.is_symlink() and sha(path) == row['sha256'], 'changed block input ' + str(path))
    return path

def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix='.' + path.name + '.', dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, 'w') as handle:
            json.dump(value, handle, indent=2, allow_nan=False)
            handle.write('\n')
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()

def own_path(path, fresh=False):
    path = Path(path).resolve()
    need(path.is_relative_to(STUDY), 'output outside own study')
    if fresh:
        need(not path.exists(), 'fresh output required')
    return path

def process_birth(pid):
    try:
        return Path('/proc/' + str(pid) + '/stat').read_text().rsplit(')', 1)[1].split()[19]
    except FileNotFoundError:
        return None

def host_available():
    info = {line.split(':')[0]: int(line.split()[1]) * 1024 for line in Path('/proc/meminfo').read_text().splitlines()}
    available = info['MemAvailable']
    group = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::')[1].lstrip('/')
    while group.is_relative_to('/sys/fs/cgroup'):
        try:
            cap = (group / 'memory.max').read_text().strip()
            if cap != 'max':
                available = min(available, max(0, int(cap) - int((group / 'memory.current').read_text())))
        except FileNotFoundError:
            pass
        if group == Path('/sys/fs/cgroup'):
            break
        group = group.parent
    return available

GLOBAL_ADMIN = STUDY.parent / 'EXPOSURE_LONGCHAIN_20261117_V1_RESOURCES'

def unit_alive(row):
    unit = row.get('unit')
    need(isinstance(unit, str) and re.fullmatch(r'[A-Za-z0-9_.@-]+', unit), 'invalid shared administrative unit')
    state = ctl('show', unit, '--property=ActiveState', '--property=ControlGroup')
    values = dict(line.split('=', 1) for line in state.stdout.splitlines() if '=' in line)
    if values.get('ActiveState') in {'active', 'activating', 'reloading', 'deactivating'}:
        return True
    raw = values.get('ControlGroup') or row.get('cgroup')
    if isinstance(raw, str) and raw.startswith('/'):
        group = Path('/sys/fs/cgroup') / raw.lstrip('/')
        if group.is_relative_to('/sys/fs/cgroup'):
            try:
                return bool((group / 'cgroup.procs').read_text().strip())
            except FileNotFoundError:
                pass
    return False

def expected_unit(block_id, run_id):
    return 'ieantn-deep-a-' + hashlib.sha256((block_id + run_id).encode()).hexdigest()[:16] + '.service'

def reserve(block):
    # Keep this shared lock through startup so another compliant coordinator never sees
    # an unlaunched reservation as stale. No research or mathematical content is shared.
    GLOBAL_ADMIN.mkdir(exist_ok=True)
    handle = (GLOBAL_ADMIN / 'allocations.lock').open('a')
    fcntl.flock(handle, fcntl.LOCK_EX)
    registry = GLOBAL_ADMIN / 'allocations.json'
    try:
        document = load(registry) if registry.exists() else {'schema': 'EXPOSURE_LONGCHAIN_RESOURCE_ALLOCATIONS_V1', 'allocations': []}
        need(document.get('schema') == 'EXPOSURE_LONGCHAIN_RESOURCE_ALLOCATIONS_V1', 'shared resource schema')
        rows = document['allocations']
        active = [row for row in rows if unit_alive(row)]
        ours = [row for row in active if row.get('participant') == 'A']
        need(sum(row['memory_bytes'] for row in active) + 192 * GiB <= 384 * GiB, 'global A+B memory reservation exceeded')
        need(sum(row['cpus'] for row in active) + 24 <= 48, 'global A+B CPU reservation exceeded')
        need(sum(row['scratch_bytes'] for row in active) + 75 * GiB <= 300 * GiB, 'global A+B scratch reservation exceeded')
        need(sum(row['memory_bytes'] for row in ours) + 192 * GiB <= 192 * GiB and
             sum(row['cpus'] for row in ours) + 24 <= 24 and
             sum(row['scratch_bytes'] for row in ours) + 75 * GiB <= 150 * GiB,
             'A discovery resource allowance already reserved')
        requested = set(sum(CPU_SLOTS, []))
        need(requested.issubset(os.sched_getaffinity(0)), 'reserved A discovery CPU slots unavailable')
        for row in active:
            need(not requested.intersection(row['CPU_affinity']), 'foreign or own active CPU reservation overlaps A discovery block')
        available = host_available()
        free = shutil.disk_usage(STUDY).free
        need(available >= 512 * GiB + 192 * GiB + sum(row['memory_bytes'] for row in active),
             'actual host RAM cannot preserve512GiB plus outstanding reservations')
        # Unknown foreign scratch consumption is conservatively taken as zero usage;
        # retain room for the full remaining300GiB instead of inferring free RAM from disk.
        need(free >= (1024 + 300) * GiB, 'actual free disk cannot preserve1TiB plus remaining global scratch')
        fresh = [{'participant': 'A', 'run': row['run_id'], 'unit': expected_unit(block['block_id'], row['run_id']),
                  'cgroup': None, 'memory_bytes': 64 * GiB, 'cpus': 8,
                  'CPU_affinity': CPU_SLOTS[index], 'scratch_bytes': 25 * GiB}
                 for index, row in enumerate(block['runs'])]
        # Preserve every foreign row, including drained rows; remove only our independently
        # checked drained reservations. No other participant's workspace or results are read.
        kept = [row for row in rows if row.get('participant') != 'A' or unit_alive(row)]
        document['allocations'] = kept + fresh
        atomic(registry, document)
        observation = {'participant': 'A', 'reserved_units': fresh, 'MemAvailable_bytes': available,
                       'free_disk_bytes': free, 'global_memory_max_bytes': 384 * GiB,
                       'global_CPU_max': 48, 'global_scratch_max_bytes': 300 * GiB,
                       'A_memory_max_bytes': 192 * GiB, 'A_CPU_max': 24, 'A_scratch_max_bytes': 150 * GiB,
                       'counterpart_handshake': 'NO_DESIGNATED_B_ACKNOWLEDGEMENT; B_COMPLIANCE_UNKNOWN',
                       'scope': 'Shared administrative reservations only; actual host headroom independently checked.'}
        return observation, handle
    except BaseException:
        handle.close()
        raise

def publish_started_reservations(block):
    registry = GLOBAL_ADMIN / 'allocations.json'
    document = load(registry)
    units = {expected_unit(block['block_id'], row['run_id']) for row in block['runs']}
    for row in document['allocations']:
        if row.get('participant') == 'A' and row['unit'] in units:
            status = ctl('show', row['unit'], '--property=ControlGroup', '--value')
            row['cgroup'] = status.stdout.strip() or None
    atomic(registry, document)

def release(block):
    registry = GLOBAL_ADMIN / 'allocations.json'
    with (GLOBAL_ADMIN / 'allocations.lock').open('a') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        document = load(registry)
        units = {expected_unit(block['block_id'], row['run_id']) for row in block['runs']}
        retained = []
        for row in document['allocations']:
            if row.get('participant') == 'A' and row['unit'] in units:
                need(not unit_alive(row), 'cannot release an owned unit that is still active')
            else:
                retained.append(row)
        document['allocations'] = retained
        atomic(registry, document)

def validate_block(path):
    block = load(path)
    need(block.get('schema') == 'DEEP_TERTIARY_BLOCK_LOCK_V1', 'block lock schema')
    need(isinstance(block.get('block_id'), str) and re.fullmatch(r'[A-Za-z0-9_-]{1,100}', block['block_id']), 'block id')
    need(block.get('phase') in {'PILOT', 'MAIN', 'ADDITIONAL'}, 'block phase')
    expected_quota_guard = 75 if block['phase']=='PILOT' else 80
    need(block.get('concurrency') == 3 and block.get('quota_stop_used_percent') == expected_quota_guard, 'fixed balanced block/quota policy')
    need(len(block.get('runs', [])) == 3 and {row.get('arm') for row in block['runs']} == {'NL', 'PNT', 'IEANTN'}, 'balanced block must contain exactly three arms')
    resources = None
    seen = set()
    for row in block['runs']:
        lockpath = pin(row['execution_lock'])
        lock = load(lockpath)
        need(lock.get('schema') == 'DEEP_TERTIARY_EXECUTION_LOCK_V1', 'child execution lock schema')
        need(row['run_id'] == lock.get('run_id') and row['arm'] == lock.get('arm'), 'run/arm lock association')
        need(row['run_id'] not in seen and re.fullmatch(r'[A-Za-z0-9_-]{1,100}', row['run_id']), 'duplicate or invalid run id')
        seen.add(row['run_id'])
        need(lock.get('phase') == block['phase'] and lock.get('model') == block.get('model') and lock.get('effort') == block.get('effort'), 'common block model/phase settings')
        r = lock['resources']
        need(r['memory_gib'] == 64 and r['cpus'] == 8 and r['scratch_gib'] == 24, 'fixed matched resources required')
        need(0 < r['wall_seconds'] <= 7200 and r['generated_tokens'] > 0 and r['operations'] > 0 and r['responses'] > 0, 'positive bounded discovery budget')
        if resources is None:
            resources = r
        need(r == resources, 'all arms must have identical discovery budgets')
        for name in ['packet_manifest', 'runtime_manifest', 'protocol', 'preflight']:
            pin(lock[name])
        for item in lock['source_pins']:
            pin(item)
        need(not (STUDY / 'runs' / row['run_id']).exists(), 'fixed run already started; no research-session retry')
    return block

def quota(out, block):
    receipt = out / 'QUOTA_AND_MODEL_CATALOG.json'
    command = [sys.executable, '-I', '-B', str(STUDY / 'scripts/native_controller_v2.py'), '--catalog-only', str(receipt)]
    run = subprocess.run(command, capture_output=True, text=True, timeout=60)
    (out / 'quota.stdout').write_text(run.stdout)
    (out / 'quota.stderr').write_text(run.stderr)
    need(run.returncode == 0 and receipt.exists(), 'read-only native quota query failed; no block launched')
    record = load(receipt)
    need(any(row.get('id') == block['model'] for row in record.get('catalog', {}).get('data', [])), 'fixed common model not offered; no block launched')
    primary = record.get('rate_limits', {}).get('rateLimits', {}).get('primary')
    if not isinstance(primary, dict):
        primary = record.get('rate_limits', {}).get('rateLimitsByLimitId', {}).get('codex', {}).get('primary')
    need(isinstance(primary, dict), 'native quota unavailable; no block launched')
    used = primary.get('usedPercent')
    need(isinstance(used, (int, float)) and not isinstance(used, bool) and math.isfinite(used) and 0 <= used <= 100, 'invalid native quota observation')
    return {'used_percent': used, 'stop_used_percent': block['quota_stop_used_percent'], 'window_minutes': primary.get('windowDurationMins'),
            'resets_at': primary.get('resetsAt'), 'receipt_sha256': sha(receipt), 'no_model_inference': True}

def ctl(*args):
    return subprocess.run(['systemctl', '--user', *args], capture_output=True, text=True, timeout=10)

def cgroup_sample(unit):
    query = ctl('show', unit, '--property=ControlGroup', '--value')
    path = query.stdout.strip()
    if query.returncode or not path.startswith('/'):
        return {'available': False}
    group = Path('/sys/fs/cgroup') / path.lstrip('/')
    row = {'available': group.is_dir(), 'cgroup': str(group), 'monotonic': time.monotonic()}
    for name in ['memory.current', 'memory.peak', 'memory.max', 'memory.swap.current', 'memory.swap.max', 'memory.events', 'cpu.stat', 'cpu.max', 'cgroup.procs']:
        try:
            value = (group / name).read_text().strip()
            row[name] = int(value) if value.isdigit() else value
        except FileNotFoundError:
            row[name] = None
    # Read only statvfs metadata through this owned unit's private process roots.
    # This never enumerates worker files or reveals another arm's mathematics.
    private = []
    seen = set()
    for pid in str(row.get('cgroup.procs') or '').splitlines():
        if not pid.isdigit():
            continue
        try:
            namespace = os.readlink('/proc/' + pid + '/ns/mnt')
            if namespace in seen or namespace == os.readlink('/proc/self/ns/mnt'):
                continue
            values = {}
            for name in ['work', 'tmp']:
                fs = os.statvfs('/proc/' + pid + '/root/' + name)
                values[name] = {'capacity_bytes': fs.f_blocks * fs.f_frsize,
                                'used_bytes': (fs.f_blocks - fs.f_bfree) * fs.f_frsize}
            if values['work']['capacity_bytes'] > 26 * GiB:
                continue
            seen.add(namespace)
            private.append({'mount_namespace': namespace, 'filesystems': values})
        except (FileNotFoundError, PermissionError, ProcessLookupError, OSError):
            continue
    row['owned_private_tmpfs_metadata'] = private
    return row

def events(value):
    if not isinstance(value, str):
        return None
    return {row.split()[0]: int(row.split()[1]) for row in value.splitlines()}

def owned_file_usage(root):
    apparent = allocated = 0
    if not root.exists():
        return {'apparent_bytes': 0, 'allocated_bytes': 0}
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [name for name in dirs if not (Path(parent)/name).is_symlink()]
        for name in files:
            path = Path(parent) / name
            try:
                value = path.lstat()
            except FileNotFoundError:
                continue
            if path.is_symlink():
                continue
            apparent += value.st_size
            allocated += value.st_blocks * 512
    return {'apparent_bytes': apparent, 'allocated_bytes': allocated}

def stop_owned_run(run, reason):
    need(re.fullmatch(r'ieantn-deep-a-[a-f0-9]{16}\.service', run['unit']) is not None,
         'refuse stop outside exact owned unit namespace')
    if run.get('stop_issued'):
        return
    run['stop_issued'] = True
    run['external_interruption'] = reason
    # GNUtime is MainPID, so signal the entire owned cgroup, never MainPID alone.
    first = ctl('kill', '--kill-who=all', '--signal=SIGINT', run['unit'])
    run['stop_actions'] = [{'action': 'all_owned_cgroup_SIGINT', 'exit_code': first.returncode}]
    try:
        stopped = subprocess.run(['systemctl', '--user', 'stop', run['unit']],
                                 capture_output=True, text=True, timeout=15)
        run['stop_actions'].append({'action': 'bounded_systemd_stop_TimeoutStopSec10', 'exit_code': stopped.returncode})
    except subprocess.TimeoutExpired:
        forced = ctl('kill', '--kill-who=all', '--signal=SIGKILL', run['unit'])
        run['stop_actions'].append({'action': 'owned_cgroup_SIGKILL_after_stop_timeout', 'exit_code': forced.returncode})

def finish_run(run):
    run['stdout'].close()
    run['stderr'].close()
    samples = run['samples']
    peaks = [row['memory.peak'] for row in samples if isinstance(row.get('memory.peak'), int)]
    currents = [row['memory.current'] for row in samples if isinstance(row.get('memory.current'), int)]
    event_rows = [events(row.get('memory.events')) for row in samples if events(row.get('memory.events')) is not None]
    status = ctl('show', run['unit'], '--property=Result', '--property=ExecMainStatus', '--property=CPUUsageNSec', '--property=MemoryPeak')
    actual_result = None
    resultpath = run['output'] / 'result.json'
    if resultpath.is_file():
        actual_result = load(resultpath)
    failure = 'NOT_YET_MATHEMATICALLY_EVALUATED'
    if run.get('external_interruption'):
        failure = 'EXTERNAL_RESOURCE_OR_OWNER_INTERRUPTION_DRAFTS_PRESERVED_NOT_MATH_FAILURE'
    elif not actual_result or run['process'].returncode != 0 or actual_result.get('infrastructure_error'):
        failure = 'RESOURCE_OR_CONTROLLER_FAILURE_NOT_MATHEMATICAL_FAILURE'
    elif actual_result.get('original_valid_submission_for_evaluation') or actual_result.get('within_budget_locked_execution_prefix_available'):
        failure = 'LOCKED_WITHIN_BUDGET_CANDIDATE_PENDING_MATH_REVIEW'
    else:
        failure = 'BUDGET_OR_SUBMISSION_INCOMPLETE_PENDING_DRAFT_REVIEW'
    rusage = {}
    rusage_path = run['resource_dir'] / 'process-rusage.txt'
    if rusage_path.is_file():
        for line in rusage_path.read_text().splitlines():
            if ': ' in line:
                key, value = line.strip().rsplit(': ', 1)
                rusage[key] = value
    maximum_single = rusage.get('Maximum resident set size (kbytes)')
    tmpfs_values = [sum(value['used_bytes'] for value in namespace['filesystems'].values())
                    for sample in samples for namespace in sample.get('owned_private_tmpfs_metadata', [])]
    receipt = {'run_id': run['run_id'], 'unit': run['unit'], 'command': run['command'],
        'exit_code': run['process'].returncode, 'elapsed_seconds': time.monotonic() - run['started'],
        'external_interruption': run.get('external_interruption'), 'stop_actions': run.get('stop_actions', []),
        'status': failure, 'actual_systemd_result': status.stdout.strip(),
        'maximum_observed_cgroup_memory_peak_bytes': max(peaks) if peaks else None,
        'sampled_charged_RAM_lower_bound_bytes': max(currents) if currents else None,
        'exact_final_peak_RAM_bytes': None,
        'maximum_single_process_or_descendant_RSS_bytes': int(maximum_single) * 1024 if maximum_single and maximum_single.isdigit() else None,
        'GNU_time_process_resource_usage': rusage,
        'GNU_time_qualification': 'Actual GNU time maximum process/descendant RSS is not aggregate concurrent-process RAM.',
        'sampled_private_tmpfs_usage_lower_bound_bytes': max(tmpfs_values) if tmpfs_values else None,
        'peak_qualification': 'memory.peak is kernel peak at sample time where exposed; cgroup may disappear at exit, so exact final peak is not invented.',
        'observed_OOM_kill_events': max(row.get('oom_kill', 0) for row in event_rows) if event_rows else None,
        'OOM_qualification': 'Observed cgroup counter; nullable when unavailable, final sampling gap is disclosed.',
        'cgroup_samples': samples, 'result_sha256': sha(resultpath) if resultpath.is_file() else None,
        'worker_stop_reason': actual_result.get('stop_reason') if actual_result else None,
        'original_valid_submission_for_evaluation': actual_result.get('original_valid_submission_for_evaluation') if actual_result else False,
        'within_budget_locked_execution_prefix_available': actual_result.get('within_budget_locked_execution_prefix_available') if actual_result else False,
        'over_budget_final_is_admissible': False,
        'timely_prefix_count': len(actual_result.get('timely_locked_execution_prefixes',[])) if actual_result else 0,
        'M_status': 'PENDING_INDEPENDENT_EVALUATION', 'V_status': 'PENDING_INDEPENDENT_EVALUATION',
        'retained_run_files': owned_file_usage(run['output']),
        'retained_resource_log_files': owned_file_usage(run['resource_dir']),
        'private_work_root_max_bytes': 24 * GiB, 'private_tmp_max_bytes': GiB, 'reserved_total_private_scratch_bytes': 25 * GiB,
        'scratch_qualification': 'Private work root is capped24GiB plus a separate1GiBtmp;25GiB is reserved globally. statvfs samples are lower bounds on peak occupancy. Retained host file usage is measured separately, not called peak disk.'}
    atomic(run['resource_dir'] / 'RECEIPT.json', receipt)
    return receipt

def start_run(row, block, out, slot):
    lockpath = pin(row['execution_lock'])
    lock = load(lockpath)
    r = lock['resources']
    output = own_path(STUDY / 'runs' / row['run_id'], fresh=True)
    resource_dir = out / row['run_id']
    resource_dir.mkdir()
    unit = expected_unit(block['block_id'], row['run_id'])
    child = [sys.executable, '-I', '-B', str(STUDY / 'scripts/native_controller_v2.py'),
        '--lock', str(lockpath), '--packet-manifest', str(pin(lock['packet_manifest'])),
        '--runtime', str(pin(lock['runtime_manifest'])), '--out', str(output),
        '--phase', block['phase'], '--model', block['model'], '--effort', block['effort'],
        '--wall', str(r['wall_seconds']), '--output', str(r['generated_tokens']),
        '--operations', str(r['operations']), '--responses', str(r['responses']),
        '--memory-gib', '64', '--scratch-gib', '24', '--cpus', '8']
    command = ['systemd-run', '--user', '--unit=' + unit, '--service-type=exec', '--wait', '--pipe',
        '--setenv=PATH=/ryu/hyunsik/.nvm/versions/node/v20.20.0/bin:/usr/local/bin:/usr/bin:/bin',
        '--setenv=LC_ALL=C',
        '-p', 'MemoryMax=64G', '-p', 'MemorySwapMax=0', '-p', 'CPUQuota=800%',
        '-p', 'TasksMax=1024', '-p', 'LimitNOFILE=65536', '-p', 'TimeoutStopSec=10s',
        '-p', 'KillMode=control-group', '-p', 'SendSIGKILL=yes', '-p', 'RuntimeMaxSec=' + str(r['wall_seconds'] + 300),
        '/usr/bin/time', '-v', '-o', str(resource_dir / 'process-rusage.txt'),
        'taskset', '-c', ','.join(map(str, CPU_SLOTS[slot])), *child]
    stdout = (resource_dir / 'stdout.txt').open('xb')
    stderr = (resource_dir / 'stderr.txt').open('xb')
    process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
    record = {'run_id': row['run_id'], 'unit': unit, 'command': command, 'output': output,
        'resource_dir': resource_dir, 'stdout': stdout, 'stderr': stderr, 'process': process,
        'started': time.monotonic(), 'samples': [], 'completed': False}
    atomic(resource_dir / 'LAUNCH.json', {'run_id': row['run_id'], 'unit': unit, 'command': command,
        'launcher_pid': process.pid, 'CPU_affinity': CPU_SLOTS[slot], 'execution_lock_sha256': sha(lockpath)})
    return record

def signal_stop(number, frame):
    global stop_requested
    stop_requested = True

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--block-lock', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--reviewed-start-file', type=Path)
    parser.add_argument('--validate-only', action='store_true')
    args = parser.parse_args()
    source_before = sha(__file__)
    block = validate_block(args.block_lock)
    out = own_path(args.out, fresh=True)
    if args.validate_only:
        print(json.dumps({'status': 'VALIDATED_BLOCK_NO_QUOTA_QUERY_NO_INFERENCE', 'block_id': block['block_id']}))
        return
    need(args.reviewed_start_file is not None, 'root-reviewed start file required; no inference launch')
    review = load(args.reviewed_start_file)
    need(review.get('status') == 'ROOT_REVIEWED_START_AUTHORIZED' and
         review.get('block_lock_sha256') == sha(args.block_lock) and review.get('runner_sha256') == source_before,
         'root start review does not bind this exact block and runner')
    out.mkdir(parents=True)
    signal.signal(signal.SIGINT, signal_stop)
    signal.signal(signal.SIGTERM, signal_stop)
    atomic(out / 'START.json', {'status': 'REVIEWED_BLOCK_ADMISSION_ONLY', 'block_lock_sha256': sha(args.block_lock),
        'runner_sha256': source_before, 'review_sha256': sha(args.reviewed_start_file), 'pid': os.getpid()})
    observation = quota(out, block)
    atomic(out / 'QUOTA_GUARD.json', observation)
    if observation['used_percent'] >= observation['stop_used_percent']:
        atomic(out / 'BLOCK_STOPPED.json', {'status': 'QUOTA_GUARD_WHOLE_BALANCED_BLOCK_NOT_LAUNCHED', 'observation': observation, 'inference_calls': 0})
        print('QUOTA_GUARD_WHOLE_BALANCED_BLOCK_NOT_LAUNCHED')
        return
    reservation, startup_lock = reserve(block)
    atomic(out / 'RESERVATION.json', reservation)
    active = []
    receipts = []
    try:
        for index, row in enumerate(block['runs']):
            need(not stop_requested, 'owner stop requested before launch')
            active.append(start_run(row, block, out, index))
        # All reservations are already published under the still-held shared lock.
        # Wait only for administrative unit admission, never mathematical outcomes.
        for run in active:
            admission_deadline = time.monotonic() + 20
            while not unit_alive({'unit': run['unit'], 'cgroup': None}) and run['process'].poll() is None:
                need(time.monotonic() < admission_deadline, 'systemd unit did not enter a live resource scope')
                time.sleep(.1)
        publish_started_reservations(block)
        startup_lock.close()
        startup_lock = None
        while any(not run['completed'] for run in active):
            stop_requested_reason = ('OWNER_REQUESTED_STOP' if stop_requested else
                                     'HOST_RAM_HEADROOM_STOP' if host_available() < 512 * GiB else
                                     'HOST_DISK_HEADROOM_STOP' if shutil.disk_usage(STUDY).free < 1024 * GiB else None)
            if stop_requested_reason:
                for run in active:
                    if not run['completed']:
                        stop_owned_run(run, stop_requested_reason)
            for run in active:
                if run['completed']:
                    continue
                run['samples'].append(cgroup_sample(run['unit']))
                if run['process'].poll() is not None:
                    receipts.append(finish_run(run))
                    run['completed'] = True
            atomic(out / 'LIVE.json', {'status': 'ACTIVE_OR_DRAINING', 'completed': len(receipts), 'total': 3,
                'stop_reason': stop_requested_reason, 'no_candidate_content_read': True})
            if any(not run['completed'] for run in active):
                time.sleep(1)
        need(sha(__file__) == source_before, 'block runner source changed during execution')
        atomic(out / 'BLOCK_SEALED.json', {'status': 'ALL_THREE_FIXED_SLOTS_DRAINED_PENDING_INDEPENDENT_MATH_EVALUATION',
            'block_id': block['block_id'], 'rows': receipts, 'primary_outcomes_not_rescored': True,
            'no_mathematical_candidate_content_read': True, 'no_automatic_research_retry': True})
        print(json.dumps({'status': 'BLOCK_DRAINED', 'block_id': block['block_id'], 'completed': len(receipts)}))
    finally:
        if startup_lock is not None:
            startup_lock.close()
        for run in active:
            if run['process'].poll() is None:
                stop_owned_run(run, 'COORDINATOR_FAILURE_OR_FINALLY_CLEANUP')
                try:
                    run['process'].wait(timeout=15)
                except subprocess.TimeoutExpired:
                    run['process'].terminate()
            if not run['stdout'].closed:
                run['stdout'].close()
            if not run['stderr'].closed:
                run['stderr'].close()
        release(block)

if __name__ == '__main__':
    main()
