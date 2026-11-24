#!/usr/bin/env python3
"""Directed-Arb evaluation of an exact rational Gaussian Fourier witness.
Exact rational Sturm isolation splits every polynomial sign change. Polynomial
Gaussian integrals use their finite recurrence and their exact infinity limits,
so no sampled absolute values or truncated tails enter the result.

Tier E: analytic identities are written, not yet Lean formalized; Sympy exact
polynomial isolation and Arb arithmetic remain trusted. This is not source-first
PV, kernel certificate checking, or an RH prime-existence theorem.
"""
from pathlib import Path
import argparse,hashlib,json,time,platform,resource
import sympy as sp
import flint
from flint import arb,fmpq,ctx
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--prec',type=int,default=256);p.add_argument('--root-digits',type=int,default=45)
a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output directory required')
if a.prec<192 or a.root_digits<30:raise SystemExit('Insufficient precision requested')
a.out.mkdir(parents=True);ctx.prec=a.prec;start=time.monotonic();src=json.loads(a.candidate.read_text());coeff=[sp.Rational(s) for s in src['coefficients_decimal_exact_rationals']]
v=sp.Symbol('v');P=sp.Poly(sum(c*sp.assoc_laguerre(n,sp.Rational(-1,2),2*v) for n,c in enumerate(coeff)),v,domain=sp.QQ);Q=sp.Poly(sum((-1)**n*c*sp.assoc_laguerre(n,sp.Rational(-1,2),2*v) for n,c in enumerate(coeff)),v,domain=sp.QQ)
def A(q):
 q=sp.Rational(q);return arb(fmpq(int(q.p),int(q.q)))
def interval(lo,hi):return arb(A((lo+hi)/2),A((hi-lo)/2))
def primitive(poly,u):
 cc=list(reversed(poly.all_coeffs()));I=[arb.pi().sqrt()/2*u.erf()]
 e=(-u*u).exp()
 for k in range(1,len(cc)):I.append(arb(2*k-1)/2*I[-1]-u**(2*k-1)*e/2)
 return sum((A(c)*q for c,q in zip(cc,I)),arb(0))
def total_integral(poly):
 cc=list(reversed(poly.all_coeffs()));I=arb.pi().sqrt()/2;out=A(cc[0])*I
 for k in range(1,len(cc)):
  I=arb(2*k-1)/2*I;out+=A(cc[k])*I
 return out
def roots(poly,name):
 allroots=poly.intervals(eps=sp.Rational(1,10**a.root_digits));positive=[];encoded=[]
 for ((lo,hi),mult) in allroots:
  if lo<0<hi:raise ValueError('root straddles zero')
  encoded.append({'lower':str(lo),'upper':str(hi),'multiplicity':mult})
  if lo>=0:
   if mult!=1:raise ValueError('only simple positive roots supported')
   if lo!=hi and poly.count_roots(lo,hi)!=1:raise ValueError('Sturm interval count mismatch')
   positive.append((lo,hi))
 if poly.count_roots(0,sp.oo)!=len(positive):raise ValueError('positive root census mismatch')
 return positive,{'polynomial_low_to_high_coeffs':[str(t) for t in reversed(poly.all_coeffs())],'all_real_root_intervals':encoded,'positive_roots':len(positive),'sturm_positive_count':int(poly.count_roots(0,sp.oo))}
pRoots,pReceipt=roots(P,'P');qRoots,qReceipt=roots(Q,'Q')
def signed_piece(poly,start_u,end_u,sign):
 left=primitive(poly,start_u)
 right=total_integral(poly) if end_u is None else primitive(poly,end_u)
 return sign*(right-left)
# All positive roots are accounted for; exact polynomial signs fix every slab.
last=sp.Rational(0);last_u=arb(0);norm=arb(0);normSigns=[]
for lo,hi in pRoots:
 sample=(last+lo)/2
 value=P.eval(sample)
 if value==0:raise ValueError('zero sign sample')
 sign=1 if value>0 else -1;u=interval(lo,hi).sqrt()
 norm+=signed_piece(P,last_u,u,sign);normSigns.append({'sample':str(sample),'sign':sign});last=hi;last_u=u
value=P.eval(last+1)
if value==0:raise ValueError('zero tail sample')
sign=1 if value>0 else -1
norm+=signed_piece(P,last_u,None,sign);normSigns.append({'sample':str(last+1),'sign':sign})
norm*=2/arb.pi().sqrt()
pi=arb.pi();plo=sp.Rational(str(pi.lower().fmpq()));phi=sp.Rational(str(pi.upper().fmpq()));above=[]
for lo,hi in qRoots:
 if hi<plo:continue
 if lo>phi:above.append((lo,hi));continue
 raise ValueError('root interval overlaps pi; increase root precision')
last=phi;last_u=pi.sqrt();leak=arb(0);leakSigns=[]
for lo,hi in above:
 sample=(last+lo)/2;value=Q.eval(sample)
 if value==0:raise ValueError('zero sign sample')
 sign=1 if value>0 else -1;u=interval(lo,hi).sqrt()
 if sign==1:leak+=signed_piece(Q,last_u,u,1)
 leakSigns.append({'sample':str(sample),'sign':sign});last=hi;last_u=u
value=Q.eval(last+1)
if value==0:raise ValueError('zero tail sign')
sign=1 if value>0 else -1
if sign==1:leak+=signed_piece(Q,last_u,None,1)
leakSigns.append({'sample':str(last+1),'sign':sign});leak*=2/pi.sqrt()
F0=A(P.eval(0));J=(F0-4*leak)/norm;inv=1/J
if not (norm>0 and leak>=0 and J>1):raise ValueError('nonpositive/nonfinite objective')
receipt={'status':'PASS_DIRECTED_ARB_AND_EXACT_STURM_WRITTEN_IDENTITIES_NOT_LEAN_OR_PV','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'degree':src['degree'],'exact_coefficients_decimal':[str(c) for c in coeff],'parameters':{'precision_bits':a.prec,'root_digits':a.root_digits},'P':pReceipt,'Q':qReceipt,'P_sign_samples':normSigns,'Q_above_pi_sign_samples':leakSigns,'enclosures':{'F0':F0.str(80),'L1_norm':norm.str(80),'positive_FT_leak':leak.str(80),'J4':J.str(80),'inverse_J4':inv.str(80)},'software':{'python':platform.python_version(),'python_flint':flint.__version__,'sympy':sp.__version__},'seconds':time.monotonic()-start,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'proof_boundary':['exact Sturm operations and Arb arithmetic externally trusted','Laguerre Fourier eigenfunction and Gaussian primitive identities require formal attachment','no explicit prime-onset theorem derived','no native_decide or source-first program verification claimed']}
(a.out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','degree','seconds','enclosures']}))
