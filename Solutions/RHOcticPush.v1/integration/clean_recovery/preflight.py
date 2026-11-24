#!/usr/bin/env python3
"""Actual strict80-prefix admission without compiling or accepting the failed run."""
from pathlib import Path
import argparse, importlib.util, json, os, sys

H = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('clean_recovery_controller', H/'reproduce.py')
P = importlib.util.module_from_spec(spec)
spec.loader.exec_module(P)

def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--origin', type=Path, required=True)
    parser.add_argument('--foundation', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    P.need(not args.out.exists(), 'fresh prefix-admission receipt required')
    context = P.context()
    manifest = P.manifest_check(P.FROZEN/'capture/SOURCE_CLOSURE.json')
    maps, foundation = P.validate_foundation(args.foundation)
    result, rows = P.validate_prefix(args.origin, manifest, context, maps)
    P.need(len(rows) == 80 and result['first_recompiled_module'] == 'OcticQuadrature',
           'complete exact80 prefix and failed81 exclusion')
    receipt = {'status': 'PASS_ACTUAL80_SOURCE_COMMAND_LOG_OBJECT_AND_DEPENDENCY_ADMISSION',
               'prefix': result, 'foundation': foundation,
               'source_controller_sha256': P.sha(H/'reproduce.py'),
               'helper_sha256': P.sha(H/'resume_prefix.py'),
               'preflight_sha256': P.sha(__file__), 'python_optimization': sys.flags.optimize,
               'failed_run_accepted': False, 'remaining34_compilation_and_C_status': 'pending'}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    P.save(args.out, receipt)
    print(json.dumps({'status': receipt['status'], 'prefix_modules': len(rows),
                      'optimization': sys.flags.optimize}))

if __name__ == '__main__':
    main()
