#!/usr/bin/env python3
"""Generate an exact rational hat-basis witness from a Gaussian search seed.
The seed is untrusted: all eventual claims concern only the generated integers.
Arb generation is deterministic; this is not source-first PV or verification.
"""
from pathlib import Path
import argparse,json,hashlib
import sympy as sp
from flint import arb,fmpq,ctx
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--m',type=int,required=True);p.add_argument('--A',required=True);p.add_argument('--threshold',required=True);p.add_argument('--scale',type=int,default=10**14);a=p.parse_args()
if a.out.exists():raise SystemExit('fresh witness path required')
if a.m<1 or a.scale<1:raise SystemExit('positive mesh and scale required')
ctx.prec=192;src=json.loads(a.candidate.read_text());cs=[sp.Rational(s) for s in src['coefficients_decimal_exact_rationals']];v=sp.Symbol('v');Q=sp.Poly(sum((-1)**k*c*sp.assoc_laguerre(k,sp.Rational(-1,2),2*v) for k,c in enumerate(cs)),v,domain=sp.QQ)
qc=[arb(fmpq(int(c.p),int(c.q))) for c in Q.all_coeffs()];ints=[]
for j in range(5*a.m):
 z=arb.pi()*(arb(j)/a.m)**2;w=arb(0)
 for c in qc:w=w*z+c
 w*=(-z).exp();n=(w*a.scale+arb(1)/2).floor().unique_fmpz()
 if n is None:raise ValueError('rounding ambiguous; increase precision')
 ints.append(int(n))
rec={'m':a.m,'scale':a.scale,'coefficients':ints,'A':str(sp.Rational(a.A)),'threshold':str(sp.Rational(a.threshold)),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'untrusted_seed_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'status':'EXACT_RATIONAL_NEW_HAT_WITNESS_UNVERIFIED','source_basis':'W(t)=sum a_j tent(m*t-j), reflected evenly; terminal coefficient a_(5m)=0','not_claimed':'Gaussian identity, RH theorem, kernel verification or source-first PV'}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(rec,indent=2)+'\n');print(a.out)
