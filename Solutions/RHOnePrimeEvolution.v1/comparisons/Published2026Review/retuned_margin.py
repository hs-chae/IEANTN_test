#!/usr/bin/env python3
"""Ordinary Arb assessment of a written parameter extension of published Eq20–21.

This is a comparison experiment, not a Lean proof of the parameter extension,
not source-first PV, and not a statement literally made by the original author.
"""
from pathlib import Path
import argparse, hashlib, json, os
from flint import arb, ctx

parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
args.out.mkdir(parents=True, exist_ok=False)
ctx.prec = 192
D = arb('0.92045248904315389')
U_hi = arb('0.78353189999070')
U_lo = arb('0.78353189999069')
kappa = arb('1.101508373007')


def margin(c, t):
    return (c*D-U_hi)*t/2 + U_lo*(c*t*arb(2).log()/2).log()-kappa


rows = []
for coefficient in ['0.8301', '0.8185', '0.811', '0.8105']:
    c = arb(coefficient)
    endpoints = []
    for endpoint in ['44', '59', '60']:
        value = margin(c, arb(endpoint))
        endpoints.append({'log_x': endpoint, 'enclosure': str(value),
                          'strictly_positive': bool(value > 0),
                          'strictly_negative': bool(value < 0)})
    rows.append({'coefficient': coefficient, 'endpoints': endpoints})
selected = next(row for row in rows if row['coefficient'] == '0.811')
if not all(row['strictly_positive'] for row in selected['endpoints']):
    raise RuntimeError('claimed conservative0.811 endpoint positivity failed')
near_miss = next(row for row in rows if row['coefficient'] == '0.8105')
if not next(row for row in near_miss['endpoints'] if row['log_x'] == '60')['strictly_negative']:
    raise RuntimeError('recorded near-miss sign changed')
record = {
    'status': 'PASS_ORDINARY_ARB_COUNTERFACTUAL_COMPARISON_NOT_A_LEAN_SOURCE_EXTENSION',
    'precision_bits': 192, 'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'primary': 'BlanquerRobles2026v2,Eq15–21pp11–14;Table3p14',
    'conservative_function': '((c*D_lower-U_upper)/2)*t+U_lower*log(c*t*log(2)/2)-kappa_upper',
    'constants': {'D_lower': '0.92045248904315389', 'U_lower': '0.78353189999069',
                  'U_upper': '0.78353189999070', 'kappa_upper': '1.101508373007'},
    'results': rows,
    'written_continuum_argument': 'The function is concave for t>0: second derivative=-U_lower/t^2<0. Its positive endpoints44,60 give positive values throughout[44,60].',
    'written_parameter_argument': 'For0<c<=681/800 andx>=4e18,retain oldd*,lambda*,Delta* andallpublishedbudgetconstants as uniform bounds. Smaller c lowers actuald; poleloss,zero-remainder envelope,exterior-cost envelope,prime-power andtrivial budgets stay bounded by the oldvalues. Keep the mainc-dependence andthelog(c*t*log2/2) term explicitly.',
    'interpretation': 'Credible written-method competitor: closed/semiopen0.811 overL44..60; generic provedendpointshift would give strict-open0.8111 overL44..59. This extension and numericalpositivity have NOT been proved in Lean here and are NOT promoted into the network.',
    'near_miss': 'Negative conservative margin for0.8105 atL60 is failure of this bound, not evidence that the prime statement is false or the method optimal.'}
temporary = args.out / 'RESULT.json.fresh-tmp'
temporary.write_text(json.dumps(record, indent=2, allow_nan=False)+'\n')
os.replace(temporary, args.out / 'RESULT.json')
print(record['status'])
