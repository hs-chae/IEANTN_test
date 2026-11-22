#!/usr/bin/env python3
"""No oscillatory quadrature: exact Mellin identity plus finite directed log sums.
This computes a rigorous UPPER-BOUND EXPRESSION for the actual regularizedJ1;
the derivation relating the expression toJ1 is in BOX_MELLIN_EXACT.md.
"""
from pathlib import Path
import argparse,json,hashlib,time,sys
from rational import F,I,PI,LOG2,log,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');start=time.monotonic();N=128;sumf=I(0);sumq=I(0)
for n in range(2,N+1):
 ln=log(n);sumf+=ln/n;sumq+=ln/(n*(4*n*n-1))
lN=log(N);SN=sumf-lN**2/2
HN=1024;HG=I(sum(F(1,n)for n in range(1,HN+1)))-log(HN);gamma=I((HG-F(1,2*HN)).l,(HG-F(1,2*(HN+1))).h);aa=1-gamma-LOG2
# gamma1 >=SN-logN/(2N) by convex trapezoid, and the omittedq tail ispositive.
j1= -SN+lN/(2*N)-sumq+aa*LOG2-aa**2/2+F(1,2)+PI**2/24
need(j1.lt('.70875'),'regularizedJ1 upper cap');record={'schema':'BOX_MELLIN_EXACT_TRAPEZOID_CERTIFICATE_V1','status':'PASS','interval_semantics':'Every lower/upper row encloses a rigorous UPPER-BOUND EXPRESSION only; expression.upper bounds actualJ1. expression.lower is NOT a lower bound for actualJ1.','actual_J0_identity':'J0=log2 exactly, proved inwrittenBOX_MELLIN_EXACT.md, not claimedasLeanclosure','actual_J1_upper_expression':j1.row(),'accepted_J1_upper':'.70875','parameters':{'finite_log_terms':N,'Euler_gamma_harmonic_terms':HN,'precision_bits':256,'no_sine_cosine_evaluations':True,'gamma1_method':'convex trapezoid lower bound forN>=5','random_seed':None},'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'rational_sha256':hashlib.sha256((Path(__file__).parent/'rational.py').read_bytes()).hexdigest(),'python_optimization':sys.flags.optimize,'seconds':time.monotonic()-start,'source_first_PV':False};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k]for k in['status','actual_J1_upper_expression','seconds']},indent=2))
