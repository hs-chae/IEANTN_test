#!/usr/bin/env python3
"""Recover four exited children and execute only four never-launched trials.

This additive coordinator preserves the preregistered experiment and every old
trace. It never reads mathematical payloads or coaches a worker. Default is a
metadata-only check; research execution requires --execute-remaining.
"""
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
PINS = {
    'PROTOCOL.json': '6faf7a5ea28b576911513add4a18b9a2f546b19763b6ed61d6c9d4a286c65361',
    'TRIAL_ORDER.json': '4d01d2b1ab1a37c9c9edd2c8cf1475a964bf83307c351e29f1dc5433a35d109b',
    'PREPARED_RUNTIMES.json': 'ec815c84cca6dde487ea3f790150b886cb36a869011d6c87ff9a3bafc36244e4',
    'ACTUAL_LAUNCH_READINESS.json': 'b919912c0656843dd883c87224784034852f0989556f49e5029b28437801bc6c',
    'run.py': '9f5314f28415e775c42f7ad83b4313a637a064561dd12b80ada34494eabb95fb',
    'native_trial.py': '7b4aa2558f85f2ac242664b297eb98517ff04c63c6ff967bbe398cd33d47d269',
    '../run_screening.py': '8663604407eb2a5c48d255434c3aa1d474b6b15db5289828b2fd67e0c0dd4d88',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'Regular associated file required')
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(2**20), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    def unique(items):
        out = {}
        for key, value in items:
            need(key not in out, 'Duplicate JSON key')
            out[key] = value
        return out
    def finite(text):
        value = float(text)
        need(math.isfinite(value), 'Nonfinite JSON number')
        return value
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique,
                      parse_float=finite,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def publish(path, value):
    need(not os.path.lexists(path), 'Fresh receipt required: '+str(path))
    fd, name = tempfile.mkstemp(prefix='.resume-', dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2, allow_nan=False)
            stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        temporary.unlink()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--controller', type=Path, required=True)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--execute-remaining', action='store_true')
    args = parser.parse_args()
    controller = args.controller.resolve(strict=True)
    need(not args.run.exists(), 'Fresh additive recovery run required')
    for name, expected in PINS.items():
        need(sha(HERE/name) == expected, 'Frozen original controller/protocol differs')
    protocol = read(HERE/'PROTOCOL.json')
    prepared = read(HERE/'PREPARED_RUNTIMES.json')
    trials = prepared['trials']; order = read(HERE/'TRIAL_ORDER.json')['trials']
    need(len(trials) == len(order) == 8, 'Exactly eight preregistered trials required')
    need([row['trial'] for row in trials] == [row['id'] for row in order], 'Preregistered order differs')
    need(prepared['protocol_sha256'] == sha(HERE/'PROTOCOL.json'), 'Prepared protocol differs')
    readiness = read(HERE/'ACTUAL_LAUNCH_READINESS.json')
    need(readiness['status'] == 'READY_ALL_EIGHT_RESEARCH_LOCKS_AND_ACTUAL_NAMESPACE_PROOF_TREATMENTS_CHECKED', 'Original readiness absent')
    for row in readiness['checks']:
        need(sha(row['path']) == row['sha256'], 'Original readiness evidence changed')
    spec = importlib.util.spec_from_file_location('rh080_unchanged_resume_core', HERE.parent/'run_screening.py')
    core = importlib.util.module_from_spec(spec); spec.loader.exec_module(core)
    core.HERE = HERE
    completed = []; snapshots = {}; interpreter = None
    for index, (trial, assigned) in enumerate(zip(trials, order)):
        directory = Path(trial['directory']).resolve(strict=True)
        need(directory == controller/'trials'/trial['trial'], 'Foreign assigned trial root')
        preflight = read(directory/'PREFLIGHT.json')
        core.accept_fixture(directory, Path(preflight['fixture_lock_path']))
        result_path = directory/'research-v1/result.json'
        if index >= 4:
            for path in [directory/'RESEARCH_LOCK.json', directory/'research-v1', directory/'TRIAL_EXECUTION_SUMMARY.json']:
                need(not os.path.lexists(path), 'Pending trial was already launched; do not repeat')
            need(not list(directory.glob('*-research*.LAUNCH.json')), 'Pending launch evidence exists; do not repeat')
            continue
        lock_path = directory/'RESEARCH_LOCK.json'; lock = read(lock_path)
        need((lock['condition'], lock['task'], lock['replicate']) == (assigned['condition'], assigned['task'], assigned['replicate']), 'First-four trial identity differs')
        need(lock['fixture'] is False and lock['out'] == str(result_path.parent), 'Research lock output differs')
        need(lock['protocol']['sha256'] == sha(HERE/'PROTOCOL.json') and lock['resources'] == protocol['budgets'], 'Original protocol/budgets changed')
        launch_path = directory/(trial['trial']+'-research.LAUNCH.json'); launch = read(launch_path)
        need(launch['fixture'] is False and launch['lock_sha256'] == sha(lock_path), 'Original launch/lock association differs')
        need(launch['controller_sha256'] == PINS['native_trial.py'], 'Original executed controller differs')
        command = launch['command']; source_index = command.index(str(HERE/'native_trial.py'))
        actual_interpreter = command[source_index-1]
        interpreter = actual_interpreter if interpreter is None else interpreter
        need(actual_interpreter == interpreter and command[source_index+1:] == ['--lock', str(lock_path)], 'Original invocation differs')
        need(launch['cpus'] == list(range(32+index*4, 36+index*4)), 'Original four-core allocation differs')
        active = subprocess.run(['systemctl', '--user', 'is-active', '--quiet', launch['unit']+'.service'])
        need(active.returncode in [3, 4], 'Original child may still be active')
        stderr = directory/(trial['trial']+'-research.stderr')
        timing = directory/(trial['trial']+'-research.time')
        need('Finished with result: success\n' in stderr.read_text() and
             'Main processes terminated with: code=exited/status=0\n' in stderr.read_text(), 'No genuine successful systemd child exit')
        time_text = timing.read_text()
        need(re.search(r'^\s*Exit status: 0\s*$', time_text, re.M) is not None and 'Command terminated' not in time_text, 'No genuine GNU child exit0')
        value = read(result_path)
        need(value['mode'] == 'RH080_PROSPECTIVE_SCREEN' and value['model'] == protocol['model']['alias'] and value['effort'] == protocol['model']['reasoning_effort'], 'Recorded model/mode differs')
        for actual, frozen in [('wall', 'active_wall_seconds'), ('output', 'output_token_admission'),
                               ('operations', 'executor_operations'), ('responses', 'max_responses'),
                               ('cpus', 'cpus'), ('memory_gib', 'memory_gib'), ('scratch_gib', 'scratch_gib')]:
            need(value['limits'][actual] == protocol['budgets'][frozen], 'Recorded actual trial limit differs')
        need(launch['unit']+'.service' in value['controller_cgroup'], 'Actual child cgroup/launch association differs')
        for contract in ['MemoryMax=64G', 'MemorySwapMax=0', 'CPUQuota=400%']:
            need(contract in command, 'Original requested resource contract differs')
        need(value['credentials_mounted_in_worker'] is False and value['private_reasoning_collected'] is False, 'Recorded worker boundary differs')
        transport = result_path.parent/'executor/transport.json'
        need(sha(transport) == value['raw_program_transport_sha256'], 'Result/raw transport association differs')
        associated = [lock_path, launch_path, stderr, timing, directory/(trial['trial']+'-research.stdout'), result_path, transport]
        pins = {str(path): sha(path) for path in associated}; snapshots.update(pins)
        completed.append(dict(trial=trial['trial'], directory=str(directory), result_sha256=sha(result_path),
            files=pins, actual_child_exit=0, original_observer_reported_exit=143,
            observer_termination='External SIGTERM reported; sender unknown. Child services independently completed successfully.',
            model_calls_repeated=0, mathematical_payloads_read=False))
    need(str(Path(sys.executable).absolute()) == str(Path(interpreter).absolute()), 'Use the exact original Python interpreter')
    need(set(range(32, 48)) <= os.sched_getaffinity(0), 'Original trial CPU cores unavailable')
    need(core.available_ram() >= 512*2**30, '256GiB host reserve plus four64GiB trials unavailable')
    need(shutil.disk_usage(controller).free >= 2**40, 'Original scratch admission capacity unavailable')
    run = args.run.resolve(); run.mkdir(parents=True)
    publish(run/'PLAN.json', dict(status='CHECKED_FIRST4_CHILD_EXIT0_LAST4_NEVER_LAUNCHED_NO_NEW_INFERENCE',
        original_source_pins=PINS, overlay_sha256=sha(Path(__file__)), interpreter=interpreter,
        completed=completed, remaining=[row['trial'] for row in trials[4:]],
        execute_requested=args.execute_remaining, available_RAM_bytes=core.available_ram(),
        disk_free_bytes=shutil.disk_usage(controller).free, observer_exit=143, observer_sender='UNKNOWN',
        calendar_interruption_disclosed=True, mathematical_scoring_performed=False))
    if not args.execute_remaining:
        print(json.dumps(dict(status='PASS_RESUME_METADATA_ONLY_NO_MODEL_CALLS', first4=4, remaining4=4))); return
    for row in completed:
        directory = Path(row['directory']); recovery_path = directory/'RECOVERED_CHILD_COMPLETION_v1.json'
        need(not (directory/'TRIAL_EXECUTION_SUMMARY.json').exists(), 'Do not overwrite an existing completion summary')
        publish(recovery_path, dict(status='GENUINE_CHILD_EXIT0_ASSOCIATION_RECOVERED_AFTER_OBSERVER_TERMINATION', **row))
        value = read(directory/'research-v1/result.json')
        publish(directory/'TRIAL_EXECUTION_SUMMARY.json', dict(trial=row['trial'], result_sha256=row['result_sha256'],
            status='RECOVERED_ACTUAL_CHILD_EXIT0_REQUIRES_INDEPENDENT_MATHEMATICAL_SCORING',
            mechanical_submission_gate_passed=value.get('mechanical_submission_gate_passed'),
            stop_reason=value.get('stop_reason'), discovery_admissible_for_evaluation=value.get('discovery_admissible_for_evaluation'),
            artifact_export=value.get('artifact_export'), recovery_receipt=str(recovery_path),
            recovery_receipt_sha256=sha(recovery_path), no_mathematical_success_inferred_from_gate=True))
    original_launch = core.launch
    def fresh_label_launch(lock, fixture, slot, label):
        need(not fixture, 'Every fixture is already complete; no fixture/research repetition')
        return original_launch(lock, fixture, slot, label+'-resume-v1')
    core.launch = fresh_label_launch
    def one(pair):
        slot, trial = pair
        return core.one(trial, slot, False, 4)
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        newly_completed = list(pool.map(one, enumerate(trials[4:])))
    for path, expected in snapshots.items():
        need(sha(path) == expected, 'Original first-four evidence changed')
    for name, expected in PINS.items():
        need(sha(HERE/name) == expected, 'Original source/protocol changed during resume')
    all_summaries = [read(Path(row['directory'])/'TRIAL_EXECUTION_SUMMARY.json') for row in trials]
    destination = core.DATA/'FOLLOWUP_EXECUTION_SUMMARY.json'
    publish(destination, dict(status='ALL_EIGHT_SEPARATE_FOLLOWUP_EXECUTED_WITH_AUDITABLE_OBSERVER_RECOVERY_NOT_MATHEMATICAL_SCORING',
        trials=all_summaries, recovered_first4=completed, newly_executed_last4=[row['trial'] for row in newly_completed],
        original_results_preserved=True, no_first4_model_call_repeated=True,
        overlay_sha256=sha(Path(__file__)), calendar_interruption_disclosed=True))
    publish(run/'RESULT.json', dict(status='PASS_FIRST4_ACTUAL_COMPLETION_RECOVERED_LAST4_EXECUTED_ONCE',
        summary_sha256=sha(destination), overlay_sha256=sha(Path(__file__)), first4_evidence_unchanged=True,
        original_source_pins=PINS, no_mathematical_scoring=True))
    print(json.dumps(dict(status='PASS_FIRST4_ACTUAL_COMPLETION_RECOVERED_LAST4_EXECUTED_ONCE', completed=8)))


if __name__ == '__main__':
    main()
