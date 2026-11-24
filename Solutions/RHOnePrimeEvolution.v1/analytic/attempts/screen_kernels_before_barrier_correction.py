#!/usr/bin/env python3
"""Ordinary deterministic exploratory Fourier screening, never a certificate or PV.
Compact transforms use Gauss quadrature; L1 quadrature is truncated with a
reported analytic envelope coefficient, not a certified numerical integral.
CMS/Fejer/Gaussian objectives use scipy quadrature; error estimates are reported.
"""
from pathlib import Path
import argparse,json,time,hashlib,platform
import numpy as np
import scipy
from scipy.integrate import simpson,quad
from scipy.special import eval_hermite
from scipy.optimize import minimize_scalar
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('fresh output required')
a.out.mkdir(parents=True)
t0=time.monotonic();q,w=np.polynomial.legendre.leggauss(640);q=(q+1)/2;w=w/2
y=np.linspace(0,600,30001)
rows=[]
def integral_transform(k):
 out=np.empty(len(y))
 for n in range(0,len(y),1000):out[n:n+1000]=2*np.cos(y[n:n+1000,None]*q)@(w*k(q))
 return out
families=[]
for m in [1,2,3,4,6,8,12]:families.append((f'compact_polynomial_1_minus_tpow{2*m}',lambda t,m=m:1-t**(2*m),4*m/(2*m+1),8*m))
for r in [1,2,3]:families.append((f'compact_power_tent_r{r}',lambda t,r=r:(1-t)**r,2/(r+1),4*r))
families += [('compact_cosine',lambda t:np.cos(np.pi*t/2),4/np.pi,2*np.pi),('compact_raised_cosine',lambda t:(1+np.cos(np.pi*t))/2,1,4*np.pi),('compact_wendland_C2',lambda t:(1-t)**4*(1+4*t),2/3,80)]
for name,k,mass,tailcoef in families:
 f=integral_transform(k);i=float(simpson(np.abs(f),x=y));rows.append({'name':name,'mass':mass,'finite_Fourier_L1_half_integral':i,'cutoff':600,'tail_envelope_coefficient_A_over_y2':tailcoef,'analytic_tail_upper':tailcoef/600,'float_threshold_estimate_with_tail_upper':(i+tailcoef/600)/(np.pi*mass),'status':'FLOAT_SCREEN_NOT_CERTIFIED'})
# Box has a divergent absolute Fourier integral, and cannot enter this method.
rows.append({'name':'compact_Box','mass':2,'status':'REJECTED_DIVERGENT_ABSOLUTE_FOURIER_L1','reason':'FT=2*sin(y)/y and integral abs FT diverges'})
from scipy.special import sici
normH=sici(np.pi)[0]/2
j=lambda l:(4*np.sin(np.pi*l/2)-3)/(l*normH)
opt=minimize_scalar(lambda l:-j(l),bounds=(.7,1),method='bounded',options={'xatol':1e-13})
for l in [.9,.8924,float(opt.x)]:rows.append({'name':'CMS_cosine_quotient_H_dilation','lambda':l,'norm_H_L1':normH,'J_A4':float(j(l)),'inverse_J_A4':float(1/j(l)),'boundary_8_Fhat_at_1':float(2*np.pi*l*np.cos(np.pi*l/2)),'status':'FLOAT_SCREEN_PAPER_KERNEL_NOT_NEW_DISCOVERY'})
l=np.sqrt(3/4);jj=1/l-4*(1/l+l-2)
rows.append({'name':'Fejer_bandlimited_dilation','lambda':float(l),'J_A4':float(jj),'inverse_J_A4':float(1/jj),'status':'FLOAT_SCREEN'})
terms=[(-4.8,1,3.3),(1.5,1,7.4),(520,12,9.7),(1.3,0,2.8),(.18,0,2)]
def g(x):return sum(c*x**(2*n)*np.exp(-aa*x*x) for c,n,aa in terms)
def gh(t):return sum(c*((-1)**n)*np.sqrt(np.pi/aa)/(4*aa)**n*eval_hermite(2*n,np.pi*t/np.sqrt(aa))*np.exp(-np.pi**2*t*t/aa) for c,n,aa in terms)
norm,e1=quad(lambda x:2*abs(g(x)),0,12,epsabs=1e-11,epsrel=1e-11,limit=2000)
leak,e2=quad(lambda t:2*max(0,gh(t)),1,12,epsabs=1e-11,epsrel=1e-11,limit=2000)
for A in [4,36/11]:
 jj=(g(0)-A*leak)/norm;rows.append({'name':'CMS_published_Gaussian_polynomial_4_12','A':A,'norm_F_L1_truncated12':norm,'positive_FT_leak_truncated12':leak,'quadrature_reported_error':[e1,e2],'J':jj,'inverse_J':1/jj,'status':'FLOAT_SCREEN_NOT_CERTIFIED_NOT_NEW_KERNEL','source':'https://arxiv.org/html/1708.04122v2#S4.SS6'})
rec={'status':'EXPLORATORY_ORDINARY_NUMERICS_ONLY_NO_THEOREM_OR_PV','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-t0,'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'parameters':{'gauss_points':640,'frequency_cutoff':600,'frequency_cells':30000,'matrix_batch':1000,'no_randomness':True},'rows':rows,'binding_barrier':'For compact physical kernels the naive support/sup plus absolute Fourier inversion yields threshold>=1; proof attachment separate.'}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'status':rec['status'],'elapsed_seconds':rec['elapsed_seconds'],'candidates':len(rows)}))
for x in rows:
 if 'J' in x: print(x['name'],x['A'],x['J'],x['inverse_J'])
