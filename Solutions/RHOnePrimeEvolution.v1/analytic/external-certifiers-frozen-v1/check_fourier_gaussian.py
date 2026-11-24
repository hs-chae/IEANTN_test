#!/usr/bin/env python3
"""Independent checks of the searched Fourier convention.
First converts exact monomials via Gaussian differentiation/Hermite recurrence,
without using the Laguerre eigenvalue rule. Then evaluates actual cosine
Fourier integrals by directed complex-Arb integration, with independent tails.
These checks remain external arithmetic, not a Lean Fourier theorem or PV.
"""
from pathlib import Path
import argparse,json,hashlib,time,resource
import sympy as sp
from flint import arb,acb,fmpq,ctx
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output required')
a.out.mkdir(parents=True);ctx.prec=256;start=time.monotonic();src=json.loads(a.candidate.read_text());cs=[sp.Rational(s) for s in src['coefficients_decimal_exact_rationals']];v,w=sp.symbols('v w')
P=sp.Poly(sum(c*sp.assoc_laguerre(k,sp.Rational(-1,2),2*v) for k,c in enumerate(cs)),v,domain=sp.QQ);Q=sp.Poly(sum((-1)**k*c*sp.assoc_laguerre(k,sp.Rational(-1,2),2*v) for k,c in enumerate(cs)),v,domain=sp.QQ)
# Independent Hermite recurrence and monomial transform calculation.
H=[sp.Poly(1,w),sp.Poly(2*w,w)]
for n in range(1,2*P.degree()):H.append(2*sp.Poly(w,w)*H[-1]-2*n*H[-2])
Qdirect=sp.Poly(0,v,domain=sp.QQ)
for k,coeff in enumerate(reversed(P.all_coeffs())):
 hk=H[2*k]
 if any(exp[0]%2 for exp,coeff0 in hk.terms() if coeff0):raise ValueError('Hermite parity failure')
 qk=sp.Poly(sum(coeff0*v**(exp[0]//2) for exp,coeff0 in hk.terms()),v,domain=sp.QQ)
 Qdirect+=coeff*(-1)**k/sp.Integer(4)**k*qk
if Qdirect!=Q:raise ValueError('Fourier polynomial identity mismatch')
def A(q):
 q=sp.Rational(q);return arb(fmpq(int(q.p),int(q.q)))
pc=[A(t) for t in P.all_coeffs()];qc=[A(t) for t in Q.all_coeffs()]
def ev(cc,z):
 out=z*0
 for c in cc:out=out*z+c
 return out
# Integral tails after the substitution u=sqrt(pi)*x, entirely positive bound.
R=arb(12);U=arb.pi().sqrt()*R;T=arb.pi().sqrt()/2*U.erfc();tail=abs(A(P.nth(0)))*T
for k in range(1,P.degree()+1):
 T=arb(2*k-1)/2*T+U**(2*k-1)*(-U*U).exp()/2
 tail+=abs(A(P.nth(k)))*T
tail*=2/arb.pi().sqrt()
rows=[]
for sf in ['0','1/4','1/2','1','5/4','2','3']:
 s=A(sp.Rational(sf))
 def f(z,_analytic):
  zz=arb.pi()*z*z
  return 2*ev(pc,zz)*(-zz).exp()*(2*arb.pi()*s*z).cos()
 integral=acb.integral(f,0,12,abs_tol=arb('1e-45'),rel_tol=arb('1e-45'),eval_limit=100000)
 expected=ev(qc,arb.pi()*s*s)*(-arb.pi()*s*s).exp()
 diff=integral-acb(expected)+acb(arb(0,tail.upper()))
 if not all(z.is_finite() for z in [integral,expected,diff,tail]):raise ValueError('nonfinite integral or enclosure')
 if not diff.real.contains(0) or not diff.imag.contains(0):raise ValueError('Actual integral disagreement at '+sf)
 rows.append({'frequency':sf,'actual_direct_integral':str(integral),'expected_Fourier_polynomial':str(expected),'difference_including_independent_tail':str(diff),'contains_zero':True})
rec={'status':'PASS_EXACT_MONOMIAL_FOURIER_IDENTITY_AND_7_DIRECT_ARB_INTEGRALS','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'independent_exact_polynomial_match':True,'analytic_transform_rule':'FT[x^(2k)exp(-pi*x²)]=(-1)^k/(2pi)^(2k) d_t^(2k)exp(-pi*t²); monomialπpowerscancel','frequency_convention':'exp(-2*pi*i*x*t)','integration_cutoff':12,'allfrequency_common_tail_upper':tail.str(80),'rows':rows,'seconds':time.monotonic()-start,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'limitations':['externalArb/Sympy calculations, notLean','7integral checks do not by themselves prove all-frequency Fourieridentity','genericGaussianFT/differentiation identity stillanalytic source unlessformalized']}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'status':rec['status'],'seconds':rec['seconds'],'tail_upper':rec['allfrequency_common_tail_upper']}))
