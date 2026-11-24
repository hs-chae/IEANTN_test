#!/usr/bin/env python3
"""Ordinary screening of pre-absolute-value kernel combinations and asymmetry.
No finite integral or continuum ANT transfer is certified by this script.
"""
from pathlib import Path
import argparse,json,time,numpy as np
from scipy.integrate import simpson
from scipy.optimize import minimize_scalar
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('fresh output required')
a.out.mkdir(parents=True);start=time.monotonic();y=np.linspace(0,10000,200001);f4=np.empty_like(y);small=y<8;t,w=np.polynomial.legendre.leggauss(128);t=(t+1)/2;w=w/2
f4[small]=2*np.cos(y[small,None]*t)@(w*(1-t**8));z=y[~small];iv=1/z;sn=np.sin(z);cs=np.cos(z);f4[~small]=iv**2*(-16*cs+iv*(112*sn+iv*(672*cs+iv*(-3360*sn+iv*(-13440*cs+iv*(40320*sn+iv*(80640*cs-80640*sn*iv)))))))
a0=np.pi/2;fc=np.sinc((y+a0)/np.pi)+np.sinc((y-a0)/np.pi)
rows=[]
for alpha in [0,.1,.2,.5,1,2,4]:
 def estimate(weight):
  mass=(1-weight)*16/9+weight*4/np.pi
  M0=simpson(np.abs((1-weight)*f4+weight*fc),x=y)
  return (2*alpha+M0/np.pi)/mass
 opt=minimize_scalar(estimate,bounds=(0,1),method='bounded',options={'xatol':1e-12})
 weight=float(opt.x);mass=(1-weight)*16/9+weight*4/np.pi;tail=((1-weight)*32+weight*2*np.pi)/10000
 rows.append({'alpha':alpha,'cosine_weight':weight,'mass':mass,'C_float_from_truncated_integral':float(opt.fun),'analytic_tail_effect_upper':tail/(np.pi*mass),'pure_octic_C_float':estimate(0),'pure_cosine_C_float':estimate(1),'status':'EXPLORATORY_NO_ANT_THEOREM'})
# The odd perturbation keeps the mass and adds an imaginary Fourier component.
y2=np.linspace(0,600,30001);f=np.empty_like(y2);g=np.empty_like(y2)
for n in range(0,len(y2),1000):
 yy=y2[n:n+1000,None];f[n:n+1000]=2*np.cos(yy*t)@(w*(1-t**8));g[n:n+1000]=2*np.sin(yy*t)@(w*t*(1-t**8))
for eta in [.25,.5,.75]:
 rows.append({'asymmetric_eta':eta,'finite_even_M0':float(simpson(np.abs(f),x=y2)),'finite_asymmetric_M0':float(simpson(np.sqrt(f*f+eta*eta*g*g),x=y2)),'reason':'pointwise sqrt(u²+eta²v²)>=abs(u), so this particular odd perturbation cannot improve the same absolute Fourier objective','status':'EXPLORATORY_NUMERIC_WITH_EXACT_POINTWISE_DIAGNOSTIC'})
rec={'status':'ORDINARY_EXPLORATION_NOT_CERTIFIED_OR_PV','seconds':time.monotonic()-start,'frequency_cutoff':10000,'step':.05,'rows':rows,'absolute_kernel_bound_correction':'Elementary support+inversion onlygives1/2; the stronger published bandlimited obstruction is Cinf<=d0≈1.09769...<1.1, notthetruncatedinequalityCinf<=1.09769.'}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rows))
