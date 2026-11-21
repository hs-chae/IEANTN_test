#!/usr/bin/env python3
"""Reviewer-only exact-rational endpoint checks and post-lock comparisons.
Uniform implications use the analytic derivatives recorded in REVIEW.html.
No full Lean implication or source-first program verification is claimed.
"""
import sys,json,hashlib,datetime
from pathlib import Path
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'replay'))
import bounds as b
I,F,PI,log,exp=b.I,b.F,b.PI,b.log,b.exp
checks={}
def test(name,expr,rel,target):
 expr=b.cast(expr)
 target=I(target)
 ok=expr.gt(target) if rel=='>' else expr.lt(target)
 row={'lower':str(expr.l),'upper':str(expr.h),'relation':rel,'target':str(target.l),'passed':bool(ok)}
 checks[name]=row
 if not ok: raise ValueError('Reviewer check failed: '+name)
L=F(35);v=L/2-log(L);ellpi=log(PI)
a=2*ellpi-F(1,3)-F('1.662');d=ellpi**2-ellpi/3-F('1.148')
w=log(L)-ellpi+F(1,6)
gap=(a*v+d)/(2*PI)-F('.14')-w*w/(PI*(PI+2))
deriv=a/(2*PI)*(F(1,2)-1/L)-2*w/(PI*(PI+2)*L)
test('B5_below_all_CH_Cor12_at35_uniform_gap',gap,'>','.0666')
test('B5_CH_gap_derivative_at35',deriv,'>','.012')
test('B5_CH_linear_coefficient_positive',a,'>',0)
test('CH_minimizer_r0_derivative_negative',w,'>',0)
test('CH_minimizer_before_L_over2',L/(2*PI)-F(1,6)/PI-F(1,2),'>',0)
# Whole parameter-family comparison requested by root AFTER the lock; not arm credit.
k=log(10/PI)
test('postlock_full_A_k_lower',k,'>','1.15')
test('postlock_full_A_k_upper',k,'<','1.16')
test('postlock_log35_less_L_over8',L/8-log(L),'>',0)
coefficient=F('.158')-F('.88575')/(2*PI)
beta=F('1.15')**2-F('1.15')/3-F('1.148')
postgap=coefficient*L+beta/(2*PI)-F('.14')
test('postlock_full_A_coarse_gap_all_L35',postgap,'>','.4')
test('postlock_full_A_coarse_slope',coefficient,'>',0)
# Proper prime-tail bookkeeping for the final coupled weighted claim.
L=F(24);q=1/(2*(exp(2*L)-1))
oldUpper=F('2.09')+F('7.875')*exp(-L/6)+F('.047')*(3+4/L)+q*exp(-L/2)
repairedUpper=oldUpper+F('1.045')*L*exp(-L/2)
test('coupled_W_upper_after_missing_tail_restored',repairedUpper,'<','2.39')
low=F('.21625')*log(4)*L/(L+log(4))-F('.047')*(3+4/L)-F('1.045')*L*exp(-L/2)
test('coupled_B_conservative_lower',low,'>','.13')
# PNT parabolic correction budgets.
delta=F(35)*exp(F('-17.5'))/(2*PI)
shift=F(3,2)*exp(delta)*F('.00018')
test('B5_imaginary_displacement_budget',shift,'<','.000271')
# Explicit integrated variations used in the parabolic quadrature.
ln2=log(2)
varf=I(F(8,15)+4)
varflog=F(4,15)*(2*ln2-F(3,4))+2*(ln2+1)+F(3,2)*(ln2+F(1,2))+F(1,2)*(ln2+F(1,3))
test('parabola_variation_mass',varf,'<','4.54')
test('parabola_variation_log',varflog,'<','6.1')
test('parabola_abs_f_over_y',F(4,3)*ln2+F(2,3),'<','1.6')
margin=F('1.24')*log(2*PI*F('.33'))-F(5,6)-F('.011')-F('.0155')-F('.001')
test('parabola_full_domain_positive_surplus',margin,'>','.04')
L=F(200)
ratio=2*(F('.465')*L-F('.93')*log(L)-F('.25'))/L*F('1.0003')
test('parabola_088_full_band_ratio',ratio,'<','.88')
# Stronger unconditional CH Cor1.3 -> theta -> pi adaptation.
alpha=PI/(3*10**12)
test('CH_unconditional_relative_floor',alpha,'<','1.05e-12')
test('CH_theta_sqrt_coefficient_at_log12',I('113.67')+F('1.00000075')+3*exp(-2),'<',116)
test('CH_pi_algebraic_smaller_than_center_u100plus',F('1.05e-12')*(1+F('1.2')/100),'<','1.612e-12')
# Reuse the exact polynomial consumer with a source-correct larger 118 coefficient
# and alpha rounded UP to1.05e-12. These are REVIEWER/post-lock adapted cells.
b.Ceps=F('1.05e-12')
chcells=[]
for aa,bb in zip(b.PLANS['center'],b.PLANS['center'][1:]):
 row=b.prove_cell(aa,bb,'height')
 if row['marginMillionths']<=0:raise ValueError('Nonpositive CH adapted margin')
 chcells.append(row)
# Preserve source outputs byte-for-byte in replay logs; only inspect their exact ceilings.
qtext=(ROOT/'parabola-replay.out').read_text()
for token in ['19354/15625','491739/1000000','[829290, 570302]']:
 if token not in qtext:raise ValueError('Quadrature output mismatch '+token)
ctext=(ROOT/'finite-ram-replay.out').read_text()
for token in ['SUCCESS closed real interval [38358837683,1630650286564]','coarse passed 388741288 refined cells 1743 fine comparison points 291842','directed integer G lower bound 10786299']:
 if token not in ctext:raise ValueError('Native finite replay mismatch '+token)
ldata=(ROOT/'last-real-replay.out').read_text()
for token in ['14111427770 14111427770','1644673232 632207037 632207037','38358837682.21792636514465, 38358837682.21792636514466']:
 if token not in ldata:raise ValueError('Root replay mismatch '+token)
receipt={'schema':'FINAL_NL_REVIEWER_MATH_CHECKS_V1','completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'CH_Cor13_adapted_postlock_cells':chcells,'independent_math_review':True,'new_Lean_full_implications':False,'source_first_PV':False,'optimization_mode':sys.flags.optimize}
name='REVIEW_MATH_CHECKS'+('' if not sys.flags.optimize else '_O'+str(sys.flags.optimize))+'.json'
(ROOT/name).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'passed':True,'CH_Cor13_last_cell_margin':chcells[-1]['marginMillionths'],'optimization':sys.flags.optimize,'output':name}))
