#!/usr/bin/env python3
"""Exact rational scalar controls for the post-lock forward2.43 deduction.
The all-real proof and the unformalized starting count lemma are in PROOF.html.
This is mathematical execution evidence, not a Lean proof or source-first PV.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import argparse,sys,json,hashlib,datetime
argparse.ArgumentParser(description=__doc__).parse_args()
ROOT=Path(__file__).parent
checks={}
def check(name,value,relation,target):
 value=Q(value);target=Q(target)
 ok=value<target if relation=='<' else value>target
 if not ok:raise ArithmeticError('Failed exact control: '+name)
 checks[name]={'value':str(value),'relation':relation,'target':str(target),'passed':True}
# Positive Taylor sums are strict lower bounds for positive exp arguments.
e4lo=sum((Q(4)**k/Q(factorial(k)) for k in range(5)),Q(0))
e12lo=sum((Q(12)**k/Q(factorial(k)) for k in range(21)),Q(0))
check('exp4_lower_exceeds24_so_log24_below4',e4lo,'>',24)
check('exp12_lower_exceeds150000',e12lo,'>',150000)
C=Q(243,100);dc=Q(243,200);lc=Q(93,100)
check('D_minus_L_at24_using_log24_below4',(dc-1)*24-lc*4-Q(1,4),'>',0)
check('D_minus_L_derivative_on_ray',(dc-1)-lc/24,'>',0)
check('D_prime_upper_below_L_over2',12-dc,'>',0)
check('D_upper_is_in_source_domain',dc,'<',2)
dmax=dc*24/Q(150000)
check('delta_uniform_upper',dmax,'<',Q(1,5000))
check('delta_small_for_geometric_factors',Q(1,5000),'<',Q(1,4))
check('L_times_exp_decay_decreases',Q(1,24)-Q(1,2),'<',0)
check('L_squared_exp_decay_decreases',Q(2,24)-Q(1,2),'<',0)
# At delta<=1/4, each width factor<=1+delta; the product<=1+4delta.
t=Q(1,4)
check('exp_factor_geometric_comparison',1-t,'>',0)
check('sinh_factor_geometric_comparison',1-t-t*t,'>',0)
check('denominator_factor_comparison',1-(1+t)/24,'>',0)
check('cubic_factor_comparison',3*t+t*t,'<',1)
correction=4*C*dc*24**2/Q(150000)
check('uniform_width_correction_budget',correction,'<',Q(1,20))
check('remaining_half_unit_gap',Q(1,2)-Q(1,20),'>',0)
# Comparison coefficient arithmetic, not an audit of the other arm's proof.
check('243_less_than_full_CMS_adaptation_264',C,'<',Q(264,100))
reduction=(Q(264,100)-C)/Q(264,100)
if reduction!=Q(7,88):raise ArithmeticError('Wrong relative coefficient reduction')
# Give a directed decimal enclosure for the onset, without floating acceptance.
def exp_enclosure(t,n):
 t=Q(t)
 if t<=0 or t>=n+2:raise ValueError('Taylor tail outside domain')
 term=total=Q(1)
 for k in range(1,n+1):term=term*t/k;total+=term
 tail=(term*t/(n+1))/(1-t/(n+2))
 return total,total+tail
onlo,onhi=exp_enclosure(24,100)
check('new_onset_precedes_4e18',onhi,'<',4*10**18)
scale=10**6
onset={'lower_floor':str(Q((onlo*scale).__floor__(),scale)),'upper_ceiling':str(Q((onhi*scale).__ceil__(),scale))}
starting=Path('/data/ivy-rh-propagation-20261120/review/final-NL/draft-pinned/Intervals.md')
obj={'schema':'POST_LOCK_FORWARD243_EXACT_CONTROLS_V1','attribution':'coordinator/reviewer post-lock synthesis; not NL original discovery','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'optimization_mode':sys.flags.optimize,'statement':'RH implies #{primep:u<p<u+2.43sqrt(u)log(u)}>(1+.04/log(u))*sqrt(u)>sqrt(u), everyreal u>=exp24','starting_lemma':{'path':str(starting),'sha256':hashlib.sha256(starting.read_bytes()).hexdigest(),'lines':'158-166; proof182-230','status':'reviewed written analytic derivation plus exact-rational quadrature; not full Lean proof'},'checks':checks,'onset_directed_enclosure':onset,'relative_coefficient_reduction_vs264':str(reduction),'full_Lean_proof':False,'source_first_PV':False,'no_strict_liminf_above_one_at_exact243_claim':True}
name='CONTROLS'+('' if not sys.flags.optimize else '_O'+str(sys.flags.optimize))+'.json'
p=ROOT/(name+'.tmp');p.write_text(json.dumps(obj,indent=2)+'\n');p.replace(ROOT/name)
print(json.dumps({'checks':len(checks),'passed':True,'optimization':sys.flags.optimize,'delta_bound':str(dmax),'width_budget':str(correction),'receipt':name}))
