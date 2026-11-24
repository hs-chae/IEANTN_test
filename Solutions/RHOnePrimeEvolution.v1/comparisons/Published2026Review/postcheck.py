#!/usr/bin/env python3
"""Check the reported output enclosures against the pinned Table1 decimals.

This is ordinary postprocessing, not a formally verified checker or PV.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, os, re


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('duplicate output JSON key')
            result[key] = value
        return result
    def constant(value):
        raise ValueError('nonfinite output JSON constant:'+value)
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_constant=constant)


def upper(value):
    match = re.fullmatch(r'\[([0-9.eE+\-]+) \+/- ([0-9.eE+\-]+)\]', value)
    if match is None:
        raise ValueError('unexpected Arb enclosure representation')
    return Fraction(match.group(1))+Fraction(match.group(2))


parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
parser.add_argument('--run-root', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
if args.out.exists():
    raise ValueError('postcheck output must be fresh')
integer = read(args.run_root/'integer/stdout')
balls = read(args.run_root/'Arb/stdout')
integer_expected = {'witness-gap.json':'0.834050622349',
                    'witness-grh.json':'0.851246419624','witness-ap.json':'0.851127042054'}
arb_expected = {'witness-gap.json':'0.834050619151',
                'witness-grh.json':'0.851246416724','witness-ap.json':'0.851127036596'}
for rows, expected, label in [(integer,integer_expected,'integer'),(balls,arb_expected,'Arb')]:
    if len(rows)!=3 or {r['file'] for r in rows}!=set(expected):
        raise ValueError('incomplete witness coverage:'+label)
    for row in rows:
        if type(row['grid_size']) is not int or row['grid_size']!=1048576:
            raise ValueError('wrong grid:'+label)
        if label=='integer':
            if row['ratio_upper_bound']!=expected[row['file']]:
                raise ValueError('integer rounded result changed')
        elif not upper(row['ratio_upper_bound']) < Fraction(expected[row['file']]):
            raise ValueError('published Arb decimal not established')
record={'status':'PASS_EXACT_REPORTED_TABLE1_BOUNDS_ORDINARY_POSTPROCESSING',
        'integer':integer_expected,'Arb':arb_expected,'grid':1048576,
        'integer_stdout_sha256':hashlib.sha256((args.run_root/'integer/stdout').read_bytes()).hexdigest(),
        'Arb_stdout_sha256':hashlib.sha256((args.run_root/'Arb/stdout').read_bytes()).hexdigest(),
        'postcheck_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'boundary':'E only: no kernel/source-firstPV/program-correctness theorem'}
temporary=args.out.with_name(args.out.name+'.fresh-tmp')
with temporary.open('x') as stream:
    stream.write(json.dumps(record,indent=2,allow_nan=False)+'\n')
    stream.flush()
    os.fsync(stream.fileno())
os.replace(temporary,args.out)
print(record['status'])
