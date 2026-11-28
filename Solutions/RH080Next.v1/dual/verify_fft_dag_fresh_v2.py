#!/usr/bin/env python3
"""Independent gate for a NEW monolithic original-v2 W4 FFT cold replay.

This has no dependence on the historical 992/4/37 continuation. It proves no
new mathematics: it checks the original compiler evidence and unchanged typed
claim. Production acceptance additionally requires the actual owned supervisor.
"""
import argparse
from pathlib import Path
from reproduce_dual import context, load, need, publish, sha
import resume_fft_dag_source_cold as original
from verify_fft_dag_lineage_resume import memory_events

HERE = Path(__file__).resolve().parent


def verify_math(run, ctx, candidate):
    c = context(ctx, original.R)
    state = original.validate_prefix(run, candidate, ctx, c)
    p = state['plan']; r = load(run / 'RESULT.json')
    need(r['status'] == 'PASS_W4_COMPLETE_INTEGER_FFT_TRACE_CHECKED_TWIDDLES_AND_NUMERATOR_NOT_SOURCE_PV',
         'Original fresh source-cold mathematical replay incomplete')
    need(len(state['successful']) == len(state['rows']) and not state['incomplete'],
         'Every fresh module requires a successful exact compiler receipt')
    need(r['modules'] == len(state['rows']) and r['plan_sha256'] == sha(run / 'PLAN.json'),
         'Fresh full module/plan association differs')
    need(r['stages'] == state['proposal']['stages'] and r['N'] == state['proposal']['n']
         and r['norm_numerator'] == state['proposal']['norm_numerator'],
         'Fresh numerical statement differs from fixed candidate')
    need(r['full_original_C_FFT_PV'] is False and r['independent_fixed_claim_type_audit'] is True,
         'Incorrect verification tier or missing independently typed claim')
    need(r['SIGKILL_exits'] == 0 and original.finite_positive(r['seconds']),
         'Invalid compiler resource summary')
    need(r['max_individual_RSS_KiB'] == max(x['peak_RSS_KiB'] for x in state['successful'].values()),
         'Fresh maximum compiler RSS does not match individual receipts')
    expected = original.check_axioms(run, state); audit = load(run / 'AXIOM_AUDIT.json')
    need(audit == dict(status='PASS', roots=expected) and r['audited_roots'] == len(expected),
         'Full unchanged typed/axiom audit differs')
    need(sha(run / 'CANDIDATE.json') == sha(candidate / 'PLAN.json'),
         'Frozen candidate PLAN differs')
    # The actual compiler directory is recovered from the checker-owned source
    # origin and checked in every command by validate_prefix. A copied receipt
    # bundle does not become a new compilation or lose its original command.
    return p, r, state


def verify_resources(a, p, r):
    need(r['stages'] == 24 and r['N'] == 16777216
         and r['norm_numerator'] == 7813568381279800, 'Not the locked production W4 result')
    need(all(x is not None and x.is_file() for x in
             [a.supervisor, a.command_plan, a.stdout, a.stderr]),
         'Actual completed owned supervisor receipt/logs required')
    s = load(a.supervisor); command = load(a.command_plan)
    need(s['status'] == 'COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'
         and type(s['returncode']) is int and s['returncode'] == 0 and s['failure'] is None,
         'Fresh supervised child did not complete')
    need(s['command_file_sha256'] == sha(a.command_plan) and s['command'] == command['command'],
         'Actual supervised command differs')
    expected = ['-u', str(HERE / 'reproduce_fft_dag_bounded_v1.py'), '--context', str(a.context),
                '--candidate', str(a.candidate.resolve()), '--run', str(a.run.resolve()),
                '--workers', str(p['workers']), '--worker-memory-gib', '300']
    need(command['command'][1:] == expected, 'Supervisor did not execute bounded wrapper of unchanged fresh v2 checker')
    pins = {row['path']: row['sha256'] for row in command['source_pins']}
    need(len(pins) == len(command['source_pins']), 'Duplicate execution source pin')
    for path, digest in pins.items():
        need(sha(Path(path)) == digest, 'Executed fresh source changed: ' + path)
    need(pins.get(str(HERE / 'reproduce_fft_dag_bounded_v1.py')) == sha(HERE / 'reproduce_fft_dag_bounded_v1.py'), 'Exact initial-AS300 wrapper not pinned')
    need(pins.get(str(HERE / 'reproduce_fft_dag_v2.py')) == original.ORIGINAL_DRIVER_SHA,
         'Original fresh controller not pinned')
    supervisor = HERE.parent / 'pv/supervise_resource_run.py'
    need(s['supervisor_sha256'] == pins.get(str(supervisor)) == sha(supervisor),
         'Actual public owned-resource supervisor not pinned')
    need(s['stdout_sha256'] == sha(a.stdout) and s['stderr_sha256'] == sha(a.stderr),
         'Actual supervisor log identity differs')
    need(not a.stderr.read_bytes() and a.stdout.read_text().endswith('PASS_INTEGER_FFT_NOT_C_PV\n'),
         'Missing original fresh completion marker or stderr diagnostic')
    before = s['before']; after = s['final']
    need(a.unit and a.unit.endswith('.service') and before['path'] == after['path']
         and before['path'].startswith('/sys/fs/cgroup/')
         and before['path'].endswith('/' + a.unit), 'Concrete owned cgroup differs')
    for item in [before, after]:
        need(item['memory.max'] == str(300 * 2**30) and item['memory.swap.max'] == '0',
             'Actual 300GiB/noSwap physical limits differ')
    first = memory_events(before['memory.events']); last = memory_events(after['memory.events'])
    need(set(first) == set(last), 'Actual memory event population differs')
    delta = {k: last[k] - first[k] for k in first}
    need(all(v >= 0 for v in delta.values()) and delta['oom'] == delta['oom_kill'] == 0,
         'Actual OOM event or decreasing counters')
    need(delta.get('oom_group_kill', 0) == 0, 'Actual group OOM event')
    admission = s['admission']
    need(admission['available_RAM_bytes'] >= 2**40 and admission['free_disk_bytes'] >= 2**40
         and admission['owned_scratch_bytes'] < 270 * 2**30, 'Separate actual RAM/disk admission failed')
    need(s['samples'] and original.finite_positive(s['seconds']), 'Actual telemetry missing')
    for sample in s['samples']:
        need(sample['available_RAM_bytes'] >= 256 * 2**30
             and sample['owned_scratch_bytes'] < 290 * 2**30
             and sample['cgroup']['path'] == before['path'], 'Actual reserve failed')
    return dict(actual_owned_memory_events_delta=delta, OOM_not_inferred_from_success=True,
                wall_seconds=s['seconds'], sampled_peak_not_exact=True,
                sampled_group_memory_current_max_bytes=max(int(x['cgroup']['memory.current'])
                                                            for x in s['samples']),
                supervisor_sha256=sha(a.supervisor), command_plan_sha256=sha(a.command_plan))


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['run', 'context', 'candidate', 'output']:
        ap.add_argument('--' + name, required=True, type=Path)
    for name in ['supervisor', 'command-plan', 'stdout', 'stderr']:
        ap.add_argument('--' + name, type=Path)
    ap.add_argument('--unit'); ap.add_argument('--proof-only-toy', action='store_true')
    a = ap.parse_args(); a.run = a.run.resolve(); a.candidate = a.candidate.resolve()
    p, r, state = verify_math(a.run, a.context, a.candidate)
    if a.proof_only_toy:
        need(r['stages'] == 13, 'Toy gate cannot bypass production resource evidence')
        resources = None
    else:
        resources = verify_resources(a, p, r)
    publish(a.output, dict(
        status='PASS_INDEPENDENT_ORIGINAL_W4_FFT_SOURCE_COLD_KERNEL_ONLY',
        stages=r['stages'], N=r['N'], modules=r['modules'], norm_numerator=r['norm_numerator'],
        result_sha256=sha(a.run / 'RESULT.json'), plan_sha256=sha(a.run / 'PLAN.json'),
        validator_sha256=sha(Path(__file__)), source_cold=True, source_cold_lineage=False,
        full_C_source_first_PV_claimed=False, toy_only=a.proof_only_toy,
        actual_resource_evidence=resources))
    print('PASS independent original fresh W4 FFT cold replay; kernel-only tier')


if __name__ == '__main__':
    main()
