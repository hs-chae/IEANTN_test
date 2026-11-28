#!/usr/bin/env python3
"""Wait for the owned N24 run, independently gate it, then export its format.

The observer never controls the mathematical worker. A supervisor or proof failure
produces no acceptance and no exported bank. Large immutable artifacts are linked.
"""
import argparse, os, subprocess, sys, time
from pathlib import Path
from reproduce_dual import load, need, publish, sha

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['run', 'context', 'candidate', 'supervisor', 'command-plan',
                 'stdout', 'stderr', 'observer', 'export']:
        ap.add_argument('--' + name, required=True, type=Path)
    ap.add_argument('--unit', required=True)
    ap.add_argument('--maximum-hours', type=int, default=96)
    a = ap.parse_args()
    need(1 <= a.maximum_hours <= 168, 'Bounded observer lifetime required')
    need(not os.path.lexists(a.observer) and not os.path.lexists(a.export),
         'Fresh observer and format-export destinations required')
    a.observer.mkdir(parents=True)
    scripts = [HERE / 'verify_fft_dag_nested_resume_v4.py',
               HERE / 'export_fft_dag_bank_v4.py']
    pins = {str(p): sha(p) for p in scripts}
    publish(a.observer / 'PLAN.json', dict(
        status='OBSERVER_ONLY_NO_ACCEPTANCE', source_pins=pins,
        run=str(a.run), supervisor=str(a.supervisor), command_plan=str(a.command_plan),
        unit=a.unit, export=str(a.export), maximum_hours=a.maximum_hours,
        controller_sha256=sha(Path(__file__))))
    started = time.monotonic()
    records = []
    try:
        while not a.supervisor.is_file():
            need(time.monotonic() - started < a.maximum_hours * 3600,
                 'Observer deadline reached; no acceptance')
            time.sleep(30)
        supervised = load(a.supervisor)
        need(supervised['status'] == 'COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'
             and supervised['returncode'] == 0 and supervised['failure'] is None,
             'Actual supervised run incomplete; no mathematical acceptance')
        need((a.run / 'RESULT.json').is_file(), 'Missing completed mathematical result')
        for p, digest in pins.items():
            need(sha(Path(p)) == digest, 'Observer input script changed')
        common = ['--run', str(a.run), '--context', str(a.context),
                  '--candidate', str(a.candidate), '--supervisor', str(a.supervisor),
                  '--command-plan', str(a.command_plan), '--stdout', str(a.stdout),
                  '--stderr', str(a.stderr), '--unit', a.unit]
        for mode in range(3):
            accepted = a.observer / ('INDEPENDENT_ACCEPTED_' + str(mode) + '.json')
            command = [sys.executable, *(['-' + 'O' * mode] if mode else []),
                       str(scripts[0]), *common, '--output', str(accepted)]
            out = a.observer / ('verify-' + str(mode) + '.stdout')
            err = a.observer / ('verify-' + str(mode) + '.stderr')
            with out.open('xb') as f, err.open('xb') as g:
                result = subprocess.run(command, stdout=f, stderr=g)
            need(result.returncode == 0 and accepted.is_file(),
                 'Actual all-mode independent gate rejected')
            records.append(dict(command=command, returncode=result.returncode,
                                receipt_sha256=sha(accepted), stdout_sha256=sha(out),
                                stderr_sha256=sha(err)))
        accepted = a.observer / 'INDEPENDENT_ACCEPTED_0.json'
        command = [sys.executable, str(scripts[1]), '--base', str(a.run),
                   '--context', str(a.context), '--candidate', str(a.candidate),
                   '--accepted', str(accepted), '--run', str(a.export)]
        with (a.observer / 'export.stdout').open('xb') as f, \
             (a.observer / 'export.stderr').open('xb') as g:
            result = subprocess.run(command, stdout=f, stderr=g)
        need(result.returncode == 0 and (a.export / 'RESULT.json').is_file(),
             'Accepted proof format export failed')
        for p, digest in pins.items():
            need(sha(Path(p)) == digest, 'Observer input changed during gates')
        publish(a.observer / 'RESULT.json', dict(
            status='PASS_INDEPENDENT_ALL_MODE_V4_N24_GATE_AND_FORMAT_ONLY_BANK',
            modes=records, export=str(a.export),
            export_result_sha256=sha(a.export / 'RESULT.json'),
            source_pins=pins, seconds=time.monotonic() - started,
            mathematical_worker_unchanged=True, new_compilation=False,
            monolithic_fresh_build=False, whole_C_PV_claimed=False))
    except BaseException as error:
        publish(a.observer / 'FAILURE.json', dict(
            status='NO_ACCEPTANCE_FROM_OBSERVER',
            error=type(error).__name__ + ': ' + str(error),
            seconds=time.monotonic() - started, completed_gate_modes=records,
            mathematical_worker_unchanged=True))
        raise


if __name__ == '__main__':
    main()
