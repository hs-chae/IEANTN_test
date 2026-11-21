#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
import json,sys,hashlib
B=Path(__file__).resolve().parent
rows=[]
def lt(name,a,b):
 a=F(a);b=F(b)
 if not a<b:raise RuntimeError(name)
 rows.append({'id':name,'left':str(a),'right':str(b),'strict':True})
lt('exp1_Taylor5_exceeds2.7',F(27,10),sum((F(1,1),F(1,1),F(1,2),F(1,6),F(1,24),F(1,120))))
lt('exp3.2_lower_exceeds24',24,F(27,10)**3*F(61,50))
lt('D24_lower_exceeds24',24,F(243,200)*24-F(93,100)*F(16,5)-F(1,4))
lt('D_minus_L_derivative_positive',0,F(43,200)-F(93,100*24))
lt('delta_uniform_upper',F(243,200)*24*F(10,27)**12,F(1,5000))
lt('width_correction_uniform_upper',F(59049,5000)*24**2*F(10,27)**12,F(1,20))
lt('cube_factor_condition',3*F(1,5000)+F(1,5000)**2,1)
lt('inverse_factor_condition',1+F(1,5000),24)
lt('delta_derivative_upper',F(243,200)-24/F(2),0)
out={'status':'PASS_NINE_EXACT_RATIONAL_CONSTANT_CHECKS','optimization':sys.flags.optimize,'checks':rows,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'kernel_checked':False,'source_first_PV':False}
name='CHECKS'+(''if sys.flags.optimize==0 else '_O'+str(sys.flags.optimize))+'.json'
(B/name).write_text(json.dumps(out,indent=2)+'\n');print(out['status'],sys.flags.optimize)
