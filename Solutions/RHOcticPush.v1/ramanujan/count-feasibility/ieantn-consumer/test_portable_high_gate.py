#!/usr/bin/env python3
"""Exercise the real portable reader, then reject its accepted N1000 smoke."""
from pathlib import Path
import argparse
import subprocess
import sys
import time
import reproduce as V


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--smoke', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    smoke, out = args.smoke.resolve(), args.out.resolve()
    result, plan = V.read(smoke/'RESULT.json'), V.read(smoke/'PLAN.json')
    V.need(result['status'] == 'PASS_SMOKE_1000_AND_PARAMETERIZED_HIGH_SOURCE_MODEL' and
           result['fixed_high_output_proved'] is False and plan['smoke'] is True,
           'actual accepted bounded portable smoke required')
    V.need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(smoke),
           'fresh separate gate-controls output')
    original = V.sha(smoke/'RESULT.json')
    out.mkdir()
    rows = []
    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        target = out/(mode+'-rejected-append')
        command = [sys.executable, *flags, '-B', str(Path(V.__file__).resolve()),
            '--basis-kind', 'portable-full', '--basis', str(smoke),
            '--context', plan['context'], '--out', str(target)]
        started = time.monotonic()
        cp = subprocess.run(command, capture_output=True, text=True)
        (out/(mode+'.stdout')).write_text(cp.stdout)
        (out/(mode+'.stderr')).write_text(cp.stderr)
        expected = 'accepted full-high portable basis required; smoke is not the fixed high result'
        V.need(cp.returncode != 0 and expected in cp.stderr and not target.exists() and
               V.STATUS not in cp.stdout, 'actual portable reader reaches its specific full-high gate:'+mode)
        receipt = dict(mode=mode, command=command, returncode=cp.returncode,
            expected_rejection=expected, seconds=time.monotonic()-started,
            stdout_sha256=V.sha(out/(mode+'.stdout')), stderr_sha256=V.sha(out/(mode+'.stderr')),
            output_created=False, proof_compilation=False)
        V.save(out/(mode+'.RECEIPT.json'), receipt)
        rows.append(dict(mode=mode, receipt=mode+'.RECEIPT.json',
                         receipt_sha256=V.sha(out/(mode+'.RECEIPT.json'))))
        print(mode, cp.returncode, flush=True)
    V.need(V.sha(smoke/'RESULT.json') == original, 'accepted smoke preserved')
    V.save(out/'RESULT.json', dict(status='PASS_ALL3_ACTUAL_PORTABLE_READER_SMOKE_REJECTIONS',
        checker_sha256=V.sha(V.__file__), test_source_sha256=V.sha(__file__),
        accepted_smoke_RESULT_sha256=original, cases=rows,
        qualification='Three real existing-reader readbacks followed by exact high-result gate rejection; not a full high portable execution.'))


if __name__ == '__main__':
    main()
