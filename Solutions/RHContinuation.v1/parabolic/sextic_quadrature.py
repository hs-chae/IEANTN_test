#!/usr/bin/env python3
"""Exact continuous Fourier mass/log-moment enclosures for g(u)=1-u^6.
All cells use directed rational sine/cosine; analytic variation and tail proofs
are given in SEXTIC_PROOF.md. No floating point affects acceptance.
"""
from pathlib import Path
import argparse,json,hashlib,time,sys
from rational import F,I,PI,log,trig,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--cells-per-unit',type=int,default=500);p.add_argument('--cutoff',type=int,default=100);a=p.parse_args()
need(a.cells_per_unit==500 and a.cutoff==100,'only the proved exact certificate parameters are accepted');need(not a.out.exists(),'fresh output required')
start=time.monotonic();A=a.cutoff;h=F(1,a.cells_per_unit);sh,ch=trig(h);s,c=trig(h/2);total=I(0);moment=I(0);logbin=-1;la=None
for j in range(A*a.cells_per_unit):
    x=(j+F(1,2))*h
    fx=-12*c/x**2+60*s/x**3+240*c/x**4-720*s/x**5-1440*c/x**6+1440*s/x**7
    upper=max(-fx.l,fx.h);total+=upper
    if x>1:
        idx=(8*x).__floor__()
        if idx!=logbin:logbin=idx;anchor=F(idx,8);la=log(anchor)
        logupper=la+(x-anchor)/anchor;moment+=upper*logupper
    s,c=s*ch+c*sh,c*ch-s*sh
# Proved variation bounds from splitting at4 and explicit derivative tails.
V=F(12);Vlog=F(23);W=F(4);need(V>I(0).h,'positive variation')
tail0=sum(F(coeff,(power-1)*A**(power-1))for power,coeff in [(2,12),(3,60),(4,240),(5,720),(6,1440),(7,1440)])
tail1=sum(F(coeff,(power-1)*A**(power-1))*(log(A)+F(1,power-1))for power,coeff in [(2,12),(3,60),(4,240),(5,720),(6,1440),(7,1440)])
b0=(h*total+h/2*V+tail0)/PI
b1=(h*moment+h/2*(Vlog+W)+tail1-F(12,7)+F(2,81))/PI
need(b0.lt('1.72'),'continuous Fourier mass bound failed');need(b1.lt('1.3'),'continuous Fourier log-moment failed')
rows={'schema':'SEXTIC_CONTINUOUS_DIRECTED_FOURIER_CERTIFICATE_V1','status':'PASS','interval_semantics':'Every lower/upper row encloses a rigorous UPPER-BOUND EXPRESSION only; expression.upper bounds the actual integral. row.lower is NOT a lower bound for the actual integral.','kernel':'g(u)=max(0,1-u^6) on[-1,1]','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'rational_sha256':hashlib.sha256((Path(__file__).parent/'rational.py').read_bytes()).hexdigest(),'parameters':{'cutoff':A,'cells_per_unit':a.cells_per_unit,'cells':A*a.cells_per_unit,'precision_bits':256,'trig_Taylor_terms':20},'mass_div_pi':b0.row(),'logmoment_div_pi':b1.row(),'accepted_upper_bounds':{'mass':'1.72','logmoment':'1.3'},'analytic_total_variation':{'mass':str(V),'log_positive':str(Vlog),'weighted_tail_for_log_derivative':str(W)},'seconds':time.monotonic()-start,'python_optimization':sys.flags.optimize,'evidence_tier':'exact-rational numerical enclosure plus written continuous variation/tail proof; not source-first PV'}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps({k:rows[k]for k in ['status','mass_div_pi','logmoment_div_pi','seconds','python_optimization']},indent=2))
