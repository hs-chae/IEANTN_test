#!/usr/bin/env python3
"""Actual CLI for the same source-prefix admission used by the recovery engine."""
from pathlib import Path
import argparse, importlib.util, json, os, sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--basis', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('runtime_recovery_prefix_engine', HERE/'reproduce.py')
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    output = args.out.resolve()
    engine.need(not output.exists() and not output.is_relative_to(args.run.resolve())
        and not output.is_relative_to(args.basis.resolve())
        and not output.is_relative_to(engine.R), 'fresh separate prefix CLI receipt')
    controller_sha = engine.sha(__file__)
    engine_sha, helper_sha = engine.sha(HERE/'reproduce.py'), engine.sha(HERE/'resume_prefix.py')
    context = engine.context()
    manifest = engine.manifest_check(engine.CORRECTED/'capture/SOURCE_CLOSURE.json')
    foundation, foundation_receipt = engine.validate_foundation(args.basis)
    receipt, rows = engine.validate_prefix(args.run, manifest, context, foundation)
    engine.need(len(rows) == 114 and engine.sha(__file__) == controller_sha
                and engine.sha(HERE/'reproduce.py') == engine_sha
                and engine.sha(HERE/'resume_prefix.py') == helper_sha,
                'actual complete prefix and unchanged CLI source')
    result = {'status': 'PASS_EXACT114_CURRENT_CAMPAIGN_PREFIX_NOT_WHOLE_RUN_ACCEPTANCE',
        'CLI_source_sha256': controller_sha, 'engine_sha256': engine_sha,
        'helper_sha256': helper_sha,
        'foundation': foundation_receipt, 'prefix': receipt,
        'python_optimization': sys.flags.optimize, 'native_outputs_reused': False}
    output.parent.mkdir(parents=True, exist_ok=True)
    engine.save(output, result)
    print(json.dumps({'status': result['status'], 'prefix_count': len(rows),
                      'python_optimization': sys.flags.optimize}))


if __name__ == '__main__':
    main()
