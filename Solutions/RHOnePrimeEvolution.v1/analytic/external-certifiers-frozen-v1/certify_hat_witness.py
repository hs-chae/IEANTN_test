#!/usr/bin/env python3
"""Directed Arb FFT certification of an EXACT rational hat witness.
Mathematical normalization follows Blanquer Robles2026 supplement certify.py;
implementation is independently written, with explicit finite checks and no
assert/__debug__ acceptance. Analytic identities/FFT implementation remain E,
not a complete Lean proof, source-first PV, or RH theorem.
"""
from pathlib import Path
from fractions import Fraction
import argparse,json,hashlib,time,resource
from flint import arb,acb,fmpq,ctx
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--witness',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--grid',type=int,default=2**18);p.add_argument('--prec',type=int,default=128);a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output required')
a.out.mkdir(parents=True);ctx.prec=a.prec;start=time.monotonic();d=json.loads(a.witness.read_text());m=d['m'];scale=d['scale'];coeff=[Fraction(t,scale) for t in d['coefficients']];G=a.grid
if type(m)is not int or m<1 or type(G)is not int or G<2*len(coeff) or G&(G-1):raise ValueError('invalid grid/source parameters')
if len(coeff)!=5*m:raise ValueError('unsupported support shape')
A=Fraction(d['A']);limit=Fraction(d['threshold'])
def B(q):return arb(fmpq(q.numerator,q.denominator))
def area(l,r):
 if max(l,r)<=0:return Fraction(0)
 if min(l,r)>=0:return (l+r)/2
 return max(l,r)**2/(2*abs(l-r))
f0=(2*sum(coeff)-coeff[0])/m;leak=2*sum((area(coeff[j],coeff[j+1]if j+1<len(coeff)else Fraction(0))for j in range(m,len(coeff))),Fraction(0))/m;den=f0-A*leak
if den<=0:raise ValueError('nonpositive source objective')
modes=[acb(0)]*G;modes[0]=acb(B(coeff[0]))
for j,c in enumerate(coeff[1:],1):modes[j]=modes[-j]=acb(B(c))
transformed=acb.dft(modes)
if not all(t.is_finite()for t in transformed):raise ValueError('nonfinite DFT')
trapezoid=sum((abs(z.real)for z in transformed),arb(0))/G
curvature=8*arb.pi()**2*B(sum((j*j*abs(c)for j,c in enumerate(coeff)),Fraction(0)));error=curvature/(12*G**2);norm=trapezoid+error;ratio=norm/B(den);margin=B(limit*den)-norm
if not all(z.is_finite()for z in [trapezoid,error,norm,ratio,margin]):raise ValueError('nonfinite final enclosure')
status='PASS_DIRECTED_ARB_EXACT_HAT_OBJECTIVE_NOT_LEAN_OR_PV'if margin>0 else'FAIL_TARGET_OBJECTIVE'
rec={'status':status,'witness_sha256':hashlib.sha256(a.witness.read_bytes()).hexdigest(),'validator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'A':str(A),'threshold':str(limit),'m':m,'G':G,'precision':a.prec,'exact_F0':str(f0),'exact_leak':str(leak),'exact_denominator':str(den),'enclosures':{'norm_upper':norm.str(80),'trapezoid':trapezoid.str(80),'curvature_remainder':error.str(80),'ratio_upper':ratio.str(80),'margin':margin.str(80)},'seconds':time.monotonic()-start,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'remaining':['periodization/Fourier identities must be actual proof inputs','DFT source-to-actual-sample error theorem not provided','no source-first PV','no RH analytic conclusion promoted']}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));raise SystemExit(0 if margin>0 else 1)
