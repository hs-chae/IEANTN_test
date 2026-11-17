#!/usr/bin/env python3
"""Reproduce descriptive exposure counts; no model calls or proof runs."""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import math


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    def pairs(items):
        d = {}
        for key, value in items:
            need(key not in d, 'duplicate JSON key')
            d[key] = value
        return d
    def finite(number):
        value = float(number)
        need(math.isfinite(value), 'nonfinite JSON number')
        return value
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    base = args.root.resolve()
    primary = read(base / 'Evidence/PRIMARY192_ROWS.json')
    six = read(base / 'Evidence/HELDOUT6_ROWS.json')
    a, b = primary['rows'], six['rows']
    need(len(a) == 192 and len({r['run_id'] for r in a}) == 192, 'exact unique192 primary rows')
    need(all(type(r['primary_verified']) is bool and r['condition'] in {'E','F','P','N'} for r in a),
         'strict primary outcome and arm fields')
    primary_counts = {arm: dict(successes=sum(r['primary_verified'] for r in a if r['condition']==arm),
                               total=sum(r['condition']==arm for r in a)) for arm in ['E','F','P','N']}
    need(all(v['total'] == 48 for v in primary_counts.values()), 'matched historical arm populations')
    need(len(b) == len({r['case'] for r in b}) == 6, 'exact unique6 follow-up rows')
    need({(r['task'], r['representation']) for r in b} ==
         {(task, arm) for task in ['H01','H02','H03'] for arm in ['STRUCTURED','PROSE']},
         'all six planned task/representation cells')
    need(all(type(r['original_full_formal_target']) is bool and type(r['known_target']) is bool
             and type(r['source_first_PV_by_worker']) is bool for r in b), 'strict follow-up outcome fields')
    followup = {arm: dict(complete=sum(r['original_full_formal_target'] for r in b if r['representation']==arm),
                         total=sum(r['representation']==arm for r in b)) for arm in ['STRUCTURED','PROSE']}
    value = dict(status='PASS_DESCRIPTIVE_EXPOSURE_COUNT_REPRODUCTION', primary=primary_counts,
        primary_total_successes=sum(r['primary_verified'] for r in a), followup=followup,
        followup_source_first_PV=sum(r['source_first_PV_by_worker'] for r in b),
        followup_known_target_cases=sum(r['known_target'] for r in b),
        original_scores_rescored=False, causal_claim=False,
        input_sha256={str(path.relative_to(base)): hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in [base/'Evidence/PRIMARY192_ROWS.json', base/'Evidence/HELDOUT6_ROWS.json']})
    text = json.dumps(value, indent=2, allow_nan=False) + '\n'
    if args.out:
        need(not args.out.exists(), 'fresh reproducibility output')
        args.out.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
