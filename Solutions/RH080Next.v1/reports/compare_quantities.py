#!/usr/bin/env python3
"""Exact algebra and high-precision illustrations for the reading report.

This is not a numerical premise, interval verifier, source-first PV, or Lean
proof. Its outputs must never be imported into the verified network.
"""
import argparse,hashlib,json,os,tempfile
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp

def require(ok,message):
 if not ok:raise ValueError(message)
def exact(x):return str(x)
def decimal(x):return mp.mpf(x.numerator)/x.denominator

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
 require(not a.out.exists(),'Fresh output required');mp.mp.dps=90
 q=F(20582561296,24680948495);w0=F(170212349,200000000);w1=F(1505657839,1000000000)
 s0,s1=F('0.944247'),F('1.163388');f0,f1=F(9,8),F(16,15)
 switches={'Gaussian_to_W4':(w0-q)/(2*q-w1),'W4_to_sparse':(s0-w0)/(w1-s1),'sparse_to_flat':(f0-s0)/(s1-f1),'Gaussian_to_sparse_without_W4':(s0-q)/(2*q-s1)}
 require(0<switches['Gaussian_to_W4']<switches['W4_to_sparse']<switches['sparse_to_flat'],'Curve ordering differs')
 pi=mp.pi;L=2/(pi+mp.sqrt(pi*pi+4*pi))+(2+mp.log(pi*(pi+mp.sqrt(pi*pi+4*pi)+2)/4))/pi
 def lee_capacity(c):return c-mp.log(c)/pi-L
 def lee_flat_difference(alpha):return lee_capacity(decimal(f0)+decimal(f1)*alpha)-alpha
 cross=mp.findroot(lee_flat_difference,(30,50))
 def family(m,alpha):
  require(type(m)is int and m>=1,'Positive integer family parameter required')
  return mp.mpf(2*m)/(2*m-1)*(alpha+(1+mp.log(4*m-2))/pi)
 c40=decimal(F(53867,1270));lee40=mp.findroot(lambda c:lee_capacity(c)-40,(42,43))
 fixed64_crossings=[mp.findroot(lambda alpha:lee_capacity(mp.mpf('2.1')+mp.mpf(128)/127*alpha)-alpha,bracket)for bracket in [(4,5),(120,130)]]
 asymptotic_constant=(2+mp.log(2*pi))/pi
 values=[]
 for alpha in [F(0),F(1,5),F(1),F(10),F(40)]:
  curves={'Gaussian_infimum':q*(1+2*alpha),'W4_recorded':w0+w1*alpha,'sparse':s0+s1*alpha,'flat':f0+f1*alpha,'analytic_flat64_attained':F(21,10)+F(128,127)*alpha,'old_octic_leading_line_only':F('1.02391875')+F(9,8)*alpha,'BR_v2_line1':F('.851127043')+F('1.505827')*alpha,'BR_v2_line2':F('.85124642')+F('1.505237')*alpha}
  values.append({'alpha':exact(alpha),'old_octic_source_domain_satisfied':F('1.03')<=curves['old_octic_leading_line_only']<=16,'old_octic_source_width_range':'1.03<=c<=16; explicit onset exp24 is not inherited by new eventual curves','curves':{k:exact(v)for k,v in curves.items()},'new_threshold_infimum':exact(min(curves[k]for k in ['Gaussian_infimum','W4_recorded','sparse','flat','analytic_flat64_attained'])),'analytic_family_native_illustrations':{str(m):mp.nstr(family(m,decimal(alpha)),60)for m in [16,64,66,128,512]}})
 data={'status':'REPORT_ONLY_EXACT_ALGEBRA_AND_NATIVE_MPMATH_ILLUSTRATIONS_NOT_A_PROOF','mathematical_premise':False,'source_first_PV':False,'python_mpmath':mp.__version__,'precision_decimal_digits':mp.mp.dps,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'q_exact':exact(q),'q_decimal':mp.nstr(decimal(q),70),'full_CMS_formal_source_first_dual':exact(F(100,123)),'full_CMS_published_dual':exact(F(50000,60393)),'full_CMS_new_native_interval_dual':exact(F(2000,2399)),'native_primal_dual_gap':exact(q-F(2000,2399)),'formal_primal_dual_gap':exact(q-F(100,123)),'switches_exact':{k:exact(v)for k,v in switches.items()},'switches_decimal':{k:mp.nstr(decimal(v),60)for k,v in switches.items()},'curves':values,'gaussian_requires_positive_epsilon':True,'all_population_curves_eventual_no_explicit_onset':True,'Lee_primary':'https://arxiv.org/html/2403.11814v4#S1.E4','Lee_L_equation':'https://arxiv.org/html/2403.11814v4#S1.E2','Lee_L_native':mp.nstr(L,80),'Lee_fixed_width_capacity_native':{str(c):mp.nstr(lee_capacity(c),80)for c in [3,5]},'Lee_flat_crossover_alpha_native':mp.nstr(cross,80),'Lee_capacity_at_flat_alpha40_native':mp.nstr(lee_capacity(decimal(f0)+decimal(f1)*40),80),'analytic_flat64_alpha40_exact':exact(F(53867,1270)),'analytic_flat64_alpha40_native':mp.nstr(c40,80),'Lee_capacity_at_analytic_flat64_alpha40_native':mp.nstr(lee_capacity(c40),80),'Lee_direct_alpha40_threshold_native':mp.nstr(lee40,80),'Lee_analytic_flat64_two_crossings_native':[mp.nstr(x,80)for x in fixed64_crossings],'analytic_family_large_density_written_constant_native':mp.nstr(asymptotic_constant,80),'analytic_family_large_density_written_constant_formula':'(2+log(2*pi))/pi; m~pi*alpha/2, written asymptotic only','Lee_comparison_status':'written asymptotic consequence of literal theta theorem; high-precision display only, not a Lean theorem or optimality claim','strict_endpoint_rule':'GoodCoefficient has a positive limiting margin; fixed-width rank claims at a supremum endpoint need a separate proof.'}
 a.out.parent.mkdir(parents=True,exist_ok=True)
 fd,name=tempfile.mkstemp(prefix='.comparison-',dir=a.out.parent)
 try:
  with os.fdopen(fd,'w')as f:json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(name,a.out)
 finally:os.unlink(name)
 print(json.dumps({'status':data['status'],'out':str(a.out),'Lee_crossover':data['Lee_flat_crossover_alpha_native'],'switches':data['switches_decimal']}))
if __name__=='__main__':main()
