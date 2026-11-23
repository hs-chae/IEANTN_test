#!/usr/bin/env python3
"""Directed Arb evaluation plus explicit analytic quadrature/tail bounds.

NOT Lean verification and NOT source-first PV. The mathematical remainder
justification is in OCTIC_MOMENTS_AND_TAIL.md. The output must not silently
become a Lean hypothesis proved by this Python invocation.
"""
from pathlib import Path
import argparse,hashlib,json,math,platform,sys,time
import flint
from flint import arb,ctx
p=argparse.ArgumentParser(allow_abbrev=False)
p.add_argument('--out',type=Path,required=True);p.add_argument('--T',type=int,default=1000)
p.add_argument('--denominator',type=int,default=200);p.add_argument('--prec',type=int,default=192)
a=p.parse_args()
if a.out.exists():raise SystemExit('Refusing to overwrite output')
if a.T<10 or a.denominator<1 or a.prec<128:raise SystemExit('Unsupported parameter')
ctx.prec=a.prec
N=48
coeff=[arb(16)/(math.factorial(2*k)*(2*k+1)*(2*k+9)) for k in range(N)]
def fourier(i):
 y=arb(i)/a.denominator
 if i<8*a.denominator:
  yy=y*y;s=arb(0)
  for k in reversed(range(N)):s=s*yy+((-1)**k)*coeff[k]
  tail=arb(16)*y**(2*N)/(math.factorial(2*N)*(2*N+1)*(2*N+9))
  return s+arb(0,tail.upper())
 sn=y.sin();cs=y.cos();inv=1/y
 return inv**2*(-16*cs+inv*(112*sn+inv*(672*cs+inv*(-3360*sn+inv*(-13440*cs+inv*(40320*sn+inv*(80640*cs-80640*sn*inv)))))))
start=time.monotonic();h=arb(1)/a.denominator
cell_error=arb(16)/33*h**3/12
s0=arb(0);s1=arb(0);previous=abs(fourier(0));trace=hashlib.sha256()
for i in range(1,a.T*a.denominator+1):
 current=abs(fourier(i));trace.update((str(i)+':'+current.str(70)+'\n').encode())
 cell=h*(previous+current)/2+cell_error
 s0+=cell
 if i>a.denominator:s1+=cell*(arb(i)/a.denominator).log()
 previous=current
 if i%(100*a.denominator)==0: print('completed_through',i//a.denominator,flush=True)
# Exact integral on[0,1] of F(y)log y; F is positive there.
low=arb(0)
for k in range(N):low-=((-1)**k)*coeff[k]/((2*k+1)**2)
low_tail=arb(16)/(math.factorial(2*N)*(2*N+1)**3*(2*N+9))
low+=arb(0,low_tail.upper())
t=arb(a.T);logt=t.log();tail0=arb(0);tail1=arb(0)
for k,c in enumerate([16,112,672,3360,13440,40320,80640,80640],start=2):
 tail0+=arb(c)*t**(1-k)/(k-1)
 tail1+=arb(c)*t**(1-k)*(logt/(k-1)+arb(1)/(k-1)**2)
m0=s0+tail0;m1=low+s1+tail1
if not all(v.is_finite() for v in [m0,m1,s0,s1,tail0,tail1,low]):raise SystemExit('Nonfinite enclosure')
if not m0<arb(143)/25:raise SystemExit('Failed M0<5.72')
if not m1<arb(23)/5:raise SystemExit('Failed signed M1<4.6')
if not arb(143)/25<arb(911)/500*arb.pi():raise SystemExit('Failed A comparison')
if not arb(23)/5<arb(3)/2*arb.pi():raise SystemExit('Failed B comparison')
result={'status':'PASS_DIRECTED_ARITHMETIC_WITH_WRITTEN_ANALYTIC_REMAINDERS','verification_tier':'E; numerical pipeline not Lean-verified or source-first PV','mathematical_claims':['integral_0_infinity abs(F4(y)) dy <143/25','integral_0_infinity abs(F4(y))*log(y) dy <23/5'],'parameters':{'T':a.T,'denominator':a.denominator,'cells':a.T*a.denominator,'Arb_precision_bits':a.prec,'low_Fourier_series_terms':N,'quadrature':'endpoint absolute trapezoid plus (16/33)h^3/12 per cell','log_weight':'upper endpoint on[1,T], exact series on[0,1]'},'enclosures':{k:v.str(80) for k,v in {'finite_M0_upper':s0,'finite_M1_positive_upper':s1,'negative_M1_integral':low,'tail_M0_upper':tail0,'tail_M1_upper':tail1,'M0_upper':m0,'M1_upper':m1}.items()},'endpoint_trace_sha256':trace.hexdigest(),'software':{'python':platform.python_version(),'python_flint':flint.__version__,'flint':str(flint.__FLINT_VERSION__)},'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'command':sys.argv,'wall_seconds':time.monotonic()-start,'no_Lean_acceptance':True,'source_first_PV':False}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
