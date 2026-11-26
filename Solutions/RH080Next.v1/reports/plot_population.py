#!/usr/bin/env python3
"""Reproducible scientific illustration, never a verified numerical input."""
import argparse,json,hashlib
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--w4-status',choices=['pending','verified'],default='pending');a=ap.parse_args()
 if a.out.exists():raise ValueError('Fresh figure path required')
 mp.mp.dps=60;pi=mp.pi;L=2/(pi+mp.sqrt(pi*pi+4*pi))+(2+mp.log(pi*(pi+mp.sqrt(pi*pi+4*pi)+2)/4))/pi
 q=float(F(20582561296,24680948495));x=np.linspace(0,2.6,601)
 g=lambda a:q*(1+2*a);w=lambda a:.851061745+1.505657839*a;s=lambda a:.944247+1.163388*a;f=lambda a:1.125+(16/15)*a
 a64=lambda a:2.1+(128/127)*a
 paper=lambda a:np.minimum(.851127043+1.505827*a,.85124642+1.505237*a)
 oldenv=lambda a:np.minimum.reduce([g(a),w(a),s(a),f(a)])
 env=lambda a:np.minimum(oldenv(a),a64(a))
 plt.rcParams.update({'svg.hashsalt':'RH080-population-v1','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'font.family':'DejaVu Sans','savefig.bbox':'tight'})
 fig,axes=plt.subplots(3,1,figsize=(9.1,13.4),constrained_layout=True)
 ax=axes[0]
 for fun,label,color in [(g,'Gaussian threshold (positive epsilon needed)','#7d4bac'),(w,'W4 line ('+a.w4_status+')','#156a99'),(s,'Sparse source-first C','#a94a1c'),(f,'Flat source-first C','#198060')]:ax.plot(x,fun(x),label=label,color=color,lw=1.4)
 ax.plot(x,paper(x),label='BR v2: minimum of both printed lines',c='#666',ls='--',lw=1.3);ax.plot(x,env(x),label='Best displayed threshold',c='black',lw=2.8)
 ax.set(xlim=(0,2.6),ylim=(.79,4.6),xlabel=r'Fixed population density $\alpha$',ylabel=r'Width coefficient $c$',title='Small populations: curve selection matters');ax.grid(alpha=.17);ax.legend(loc='upper left',fontsize=8,framealpha=.94)
 ax=axes[1];x=np.linspace(0,40,401);lee=[]
 for alpha in x:
  root=mp.findroot(lambda c:c-mp.log(c)/pi-L-float(alpha),(max(1.6,float(alpha)+1.5),max(2,float(alpha)+3)))
  lee.append(float(root))
 ax.plot(x,oldenv(x),label='Four numerical-witness thresholds',c='#808080',lw=1.3,ls=':');ax.plot(x,a64(x),label='New analytic flat64 (kernel-only)',c='#ca7200',lw=1.5);ax.plot(x,env(x),label='Best displayed threshold',c='black',lw=2.5);ax.plot(x,paper(x),label='BR v2 printed minimum',c='#777',ls='--');ax.plot(x,lee,label='Lee theta consequence (written)',c='#b34369',lw=1.8)
 ax.annotate('density40: 42.415 analytic\n42.738 direct Lee',xy=(40,a64(40)),xytext=(22,53),arrowprops={'arrowstyle':'->','color':'#a65b00'},fontsize=8,color='#8c4d00')
 ax.set(xlim=(0,40),ylim=(0,62),xlabel=r'Fixed population density $\alpha$',ylabel=r'Width coefficient $c$',title='Large populations: a separate analytic improvement');ax.grid(alpha=.17);ax.legend(loc='upper left',fontsize=7.5)
 ax=axes[2];large=np.geomspace(1,10000,300);family_offset=[];lee_offset=[]
 for alpha in large:
  av=mp.mpf(float(alpha));mesh=int(mp.floor(pi*av/2))+1
  width=mp.mpf(2*mesh)/(2*mesh-1)*(av+(1+mp.log(4*mesh-2))/pi)
  root=mp.findroot(lambda c:c-mp.log(c)/pi-L-av,(av+1,av+6))
  family_offset.append(float(width-av-mp.log(av)/pi));lee_offset.append(float(root-av-mp.log(av)/pi))
 ax.semilogx(large,family_offset,label='New family with rounded integer mesh (threshold)',c='#ca7200',lw=2)
 ax.semilogx(large,lee_offset,label='Direct Lee threshold (written comparison)',c='#b34369',lw=2)
 ax.axhline(float((2+mp.log(2*pi))/pi),c='#ca7200',ls=':',label='New exact asymptotic constant ~1.221634')
 ax.axhline(float(L),c='#b34369',ls=':',label='Lee constant ~1.542627')
 ax.set(xlim=(1,10000),xlabel=r'Density $\alpha$ (log scale)',ylabel=r'Excess $c-\alpha-\log(\alpha)/\pi$',title='The full real-density family has a smaller large-density allowance');ax.grid(alpha=.17);ax.legend(loc='upper right',fontsize=8)
 a.out.parent.mkdir(parents=True,exist_ok=True);fig.savefig(a.out,format='svg',metadata={'Date':None,'Description':'Native plotting illustration only, not a proof or numerical premise. Eventual curves have no explicit onset.'});plt.close(fig)
 r=dict(status='SCIENTIFIC_ILLUSTRATION_NOT_PROOF_OR_NUMERICAL_PREMISE',w4_status=a.w4_status,sha256=hashlib.sha256(a.out.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),versions=dict(matplotlib=matplotlib.__version__,numpy=np.__version__,mpmath=mp.__version__),seed=None,source_statements=['BR v2 Theorem2','Lee2403.11814v4 Theorem1.1 Eqs2,4'],endpoint_note='Gaussian and Lee roots are threshold illustrations; positive margin or epsilon is required for GoodCoefficient membership.')
 a.out.with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
if __name__=='__main__':main()
