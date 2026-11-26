#!/usr/bin/env python3
"""Reproduce actual fixed_add source/execution/integer contract and mutation controls.

By default all 109 transitive Lean sources are compiled from source with only
pinned generic libraries, followed by independent receipt and adversarial-source
validation. --reuse-run performs the latter on an existing immutable complete
run; the receipt explicitly records that continuation rather than a fresh replay.
Standalone helper correctness is not the completed ANT source-first PV chain.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def need(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic(path: Path, data: dict) -> None:
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def child(command: list[str], log: Path) -> None:
    with log.open('w') as output:
        run = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    need(run.returncode == 0, f'child failed ({run.returncode}): {log}')
    text = log.read_text()
    need(not any(bad in text for bad in ['PANIC', 'sorryAx', 'Traceback (most recent call last)']),
         f'child emitted rejected diagnostics: {log}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--context', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--reuse-run', type=Path)
    args = parser.parse_args()
    context = args.context.resolve()
    out = args.out.resolve()
    need(context.is_file(), 'missing pinned compiler context')
    need(not out.exists(), 'output already exists; preserve immutable previous results')
    out.mkdir(parents=True)
    here = Path(__file__).resolve().parent
    primary = here / 'reproduce_fft_fixed_add.py'
    validator = here / 'verify_fft_fixed_add_result.py'
    for path in [primary, validator]:
        need(path.is_file(), f'missing reproduction phase: {path}')
    started = time.monotonic()
    python = [sys.executable] + (['-OO'] if sys.flags.optimize == 2 else ['-O'] if sys.flags.optimize == 1 else [])
    commands = []
    run = args.reuse_run.resolve() if args.reuse_run else out / 'run'
    if args.reuse_run is None:
        command = python + [str(primary), '--context', str(context), '--out', str(run)]
        commands.append(command)
        child(command, out / 'primary.log')
    need((run / 'RESULT.json').is_file(), 'primary run has no complete root receipt')
    command = python + [str(validator), '--context', str(context), '--run', str(run), '--out', str(out / 'controls')]
    commands.append(command)
    child(command, out / 'controls.log')
    controls_receipt = out / 'controls' / 'RESULT.json'
    need(controls_receipt.is_file(), 'validation phase has no receipt')
    controls = json.loads(controls_receipt.read_text())
    need(controls.get('status') == 'PASS_FIXED_ADD_SOURCE_CONTRACT_AND_NATIVE_MUTATION_CONTROLS',
         'unexpected final validator status')
    need(controls.get('source_first_PV_complete') is False, 'standalone helper must not be relabeled completed PV')
    receipt = {
        'status': 'PASS_FIXED_ADD_COMPLETE_HELPER_CONTRACT_AND_CONTROLS',
        'fresh_source_cold_in_this_invocation': args.reuse_run is None,
        'source_to_ast_execution_integer_contract_complete': True,
        'source_first_PV_complete': False,
        'final_ANT_connection_pending': True,
        'context': str(context), 'context_sha256': sha(context),
        'primary_run': str(run), 'primary_result_sha256': sha(run / 'RESULT.json'),
        'validation_result': str(controls_receipt), 'validation_result_sha256': sha(controls_receipt),
        'scripts': {str(path): sha(path) for path in [Path(__file__).resolve(), primary, validator]},
        'python': sys.version, 'optimization': sys.flags.optimize,
        'PYTHONOPTIMIZE': os.environ.get('PYTHONOPTIMIZE'), 'commands': commands,
        'seconds': time.monotonic() - started,
    }
    atomic(out / 'RESULT.json', receipt)
    print(json.dumps({'status': receipt['status'], 'result': str(out / 'RESULT.json')}))


if __name__ == '__main__':
    main()
