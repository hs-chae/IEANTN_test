"""Emit exact rational data (not a proof of the external R bounds)."""
import json
import os
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from bounds import h,P,N

def q(v):
    v=F(v)
    a=f'({v.numerator} : ℚ)'
    return a if v.denominator==1 else f'{a}/{v.denominator}'

d=Path(__file__).parent
records=json.loads(Path(os.environ.get('ENVELOPE_OUT',d/'ramanujan_cells.json')).read_text())
ss=['import RationalEnvelope', '', 'namespace RHEnvelopeData', 'open RHEnvelope',
    'set_option maxHeartbeats 0', 'set_option maxRecDepth 65536', '',
    'def coeffs : List ℚ := ['+', '.join(q(v) for v in h)+']','']
for method,cells in records.items():
    ss+=['def '+method+'Cells : List Cell := [']
    rs=[]
    for c in cells:
        a=F(c['a'])
        b=F(c['b']) if c['b'] is not None else None
        l=F(c['rl_bound']);r=F(c['rr_bound'])
        pen=(a/(a-1))**5*l+2*(P(a)+4*F(factorial(N))/a**N)*r+r*r/a**4
        # round upward to prevent unnecessarily large certificate numerals
        pen=F((pen*10**12).__ceil__(),10**12)
        margin=F(c['marginMillionths']-1,10**6)
        rs.append('  ⟨'+', '.join(q(v) for v in (0 if b is None else 1/b,1/a,pen,margin))+'⟩')
    ss+= [(','+chr(10)).join(rs)+']','',
       f'theorem {method}_checks : program coeffs {method}Cells = true := by decide +kernel',
       f'#print axioms {method}_checks','']
ss+=['end RHEnvelopeData','']
Path(os.environ.get('LEAN_CELL_OUT',d/'EnvelopeData.lean')).write_text(chr(10).join(ss))
