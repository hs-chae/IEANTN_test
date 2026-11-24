#!/usr/bin/env python3
"""Actual positive/negative incremental CLI controls in normal,-O,-OO modes."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time
from reproduce import write_json

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--context', required=True, type=Path)
    parser.add_argument('--proof-bank', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / 'controls.executed.py').write_bytes(Path(__file__).read_bytes())
    bad = json.loads(args.context.read_text())
    bad['compiler_sha256'] = '0' * 64
    write_json(args.out / 'bad-hash.json', bad)
    (args.out / 'duplicate.json').write_text('{"compiler":"first",'+args.context.read_text().lstrip()[1:])
    rows = []
    started = time.monotonic()
    for index, mode in enumerate([[], ['-O'], ['-OO']]):
        positive = args.out / ('positive-' + str(index))
        base = [sys.executable, *mode, str(HERE / 'reproduce.py'),
                '--context', str(args.context), '--proof-bank', str(args.proof_bank),
                '--modules', 'FiniteGapBridge']
        variants = [('positive', base, positive, None),
                    ('bad-module', [*base[:-1], 'MissingModule'], args.out / ('bad-module-' + str(index)), 'invalid choice'),
                    ('bad-hash', [str(args.out / 'bad-hash.json') if s == str(args.context) else s for s in base], args.out / ('bad-hash-' + str(index)), 'compiler identity mismatch'),
                    ('duplicate-json', [str(args.out / 'duplicate.json') if s == str(args.context) else s for s in base], args.out / ('duplicate-' + str(index)), 'duplicate JSON key'),
                    ('reused-out', base, positive, 'FileExistsError')]
        for label, command, output, rejection in variants:
            result_path = output / 'RESULT.json'
            previous = hashlib.sha256(result_path.read_bytes()).hexdigest() if result_path.exists() else None
            t0 = time.monotonic()
            process = subprocess.run([*command, '--out', str(output)], capture_output=True)
            stem = args.out / (str(index) + '-' + label)
            stem.with_suffix('.stdout').write_bytes(process.stdout)
            stem.with_suffix('.stderr').write_bytes(process.stderr)
            if rejection is None:
                if process.returncode != 0 or not result_path.is_file():
                    raise RuntimeError('actual positive CLI failed: ' + label)
                result = json.loads(result_path.read_text())
                if result['status'] != 'PASS_INCREMENTAL_SOURCE_COMPILES':
                    raise RuntimeError('wrong positive result')
            else:
                if process.returncode == 0 or rejection.encode() not in process.stderr:
                    raise RuntimeError('wrong negative result: ' + label)
                if previous is None and result_path.exists():
                    raise RuntimeError('negative case published an acceptance result')
                if previous is not None and hashlib.sha256(result_path.read_bytes()).hexdigest() != previous:
                    raise RuntimeError('negative case modified an earlier accepted result')
            rows.append({'mode': mode, 'case': label, 'command': [*command, '--out', str(output)],
                         'returncode': process.returncode, 'seconds': time.monotonic()-t0,
                         'expected_rejection': rejection})
    write_json(args.out / 'RESULT.json', {'status': 'PASS_15_ACTUAL_CLI_DECISIONS_NORMAL_O_OO',
               'cases': rows, 'seconds': time.monotonic()-started,
               'controls_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'reproduce_sha256': hashlib.sha256((HERE / 'reproduce.py').read_bytes()).hexdigest(),
               'scope': 'incremental build frontdoor only; not source-first PV or official Comparator'})
    print('PASS', len(rows))


if __name__ == '__main__':
    main()
