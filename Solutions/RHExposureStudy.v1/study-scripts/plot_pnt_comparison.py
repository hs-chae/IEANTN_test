#!/usr/bin/env python3
"""Illustrative full-function plot; proof is the independent analytic review."""
from pathlib import Path
import csv,hashlib,json,math
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
R=Path(__file__).resolve().parents[1];O=R/'reports';O.mkdir(exist_ok=True)
mp.mp.dps=70
def values(L):
 L=mp.mpf(L);v=L/2-mp.log(L);k=mp.log(10/mp.pi)
 b=(v*v+mp.mpf('1.662')*v+mp.mpf('1.148')+L)/(2*mp.pi)+mp.mpf('.14')
 a=mp.mpf('.158')*L+((v+k)**2-(v+k)/3)/(2*mp.pi)
 def F(r):
  T=2*mp.pi*mp.exp(r);z=mp.pi/T
  return mp.pi*mp.exp(L/2)/(T-1)+mp.exp(L/2)*(z/mp.tanh(z)-1)+(r*r-r/3)/(2*mp.pi)
 lo=mp.log(mp.mpf(10)**7/(2*mp.pi));hi=L/2
 for _ in range(120):
  p=lo+(hi-lo)/3;q=hi-(hi-lo)/3
  if F(p)<F(q):hi=q
  else:lo=p
 return float(b),float(a),float(F((lo+hi)/2))
rows=[]
for i in range(251):
 L=35+i*145/250;b,a,c=values(str(L));rows.append([L,b,a,c,(c-b)/c*100])
with (O/'PNT_FULL_FUNCTION_CURVES.csv').open('w',newline='')as f:
 w=csv.writer(f);w.writerow(['log_x','NL_B5','full_A','CH_Cor1_2_min_numeric','NL_reduction_percent_vs_numeric_CH']);w.writerows(rows)
fig,axes=plt.subplots(1,2,figsize=(10.4,3.8),layout='constrained')
axes[0].plot([r[0]for r in rows],[r[1]for r in rows],label='NL parabolic B5',color='#166a54',lw=2)
axes[0].plot([r[0]for r in rows],[r[2]for r in rows],label='IEANTN variable-height A',color='#a65920',lw=1.5)
axes[0].plot([r[0]for r in rows],[r[3]for r in rows],label='CH Cor. 1.2: numerical min over T',color='#315d8c',ls='--',lw=1.5)
axes[0].set(xlabel='log x',ylabel='Coefficient of sqrt(x) in psi error');axes[0].legend(fontsize=8);axes[0].grid(alpha=.2)
axes[1].plot([r[0]for r in rows],[r[4]for r in rows],color='#166a54',lw=2)
axes[1].set(xlabel='log x',ylabel='B5 reduction versus optimized CH (%)');axes[1].grid(alpha=.2)
for ext in ['png','svg']:fig.savefig(O/('PNT_FULL_FUNCTION_COMPARISON.'+ext),dpi=160)
receipt={'kind':'ILLUSTRATIVE_SAMPLED_CURVES_NOT_A_UNIFORM_PROOF','generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'mpmath_version':mp.__version__,'matplotlib_version':matplotlib.__version__,'precision_decimal_digits':70,'range_logx':[35,180],'sample_count':251,'CH_height_constraint':'T>=1e7; numeric optimizer, not a certified optimum','uniform_comparison_proof':'review/final-NL independent analytic comparison','samples':{'35':values('35'),'330':values('330')},'files':[{'path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in O.glob('PNT_FULL_FUNCTION_*')if p.is_file()]}
(O/'PNT_PLOT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt['samples'],indent=2))
