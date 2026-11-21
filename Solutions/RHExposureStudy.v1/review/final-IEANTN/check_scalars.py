#!/usr/bin/env python3
"""Independent exact-rational series checks; ordinary arithmetic, NOT PV.

Logarithms use 2*atanh((x-1)/(x+1)) after scaling by powers of two.
Exponentials use a positive Taylor sum and a geometric remainder.
Pi uses Machin's identity and alternating arctangent remainders.
The script checks finite constants; analytic monotonicity is in REVIEW.html.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,sys,hashlib

class I:
    def __init__(self,a,b=None):
        # Outward rounding remains exact rational arithmetic and bounds size.
        d=10**65;lo=Q(a)*d;hi=Q(a if b is None else b)*d
        self.lo=Q(lo.numerator//lo.denominator,d)
        self.hi=Q(-((-hi.numerator)//hi.denominator),d)
    def __add__(self,v):
        v=iv(v);return I(self.lo+v.lo,self.hi+v.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,v):return self+-iv(v)
    def __rsub__(self,v):return iv(v)+-self
    def __mul__(self,v):
        v=iv(v);s=[a*b for a in [self.lo,self.hi]for b in[v.lo,v.hi]];return I(min(s),max(s))
    __rmul__=__mul__
    def __truediv__(self,v):
        v=iv(v)
        if v.lo<=0<=v.hi:raise ValueError('division through zero')
        return self*I(1/v.hi,1/v.lo)
    def __rtruediv__(self,v):return iv(v)/self
    def __pow__(self,n):
        if n<0:return 1/(self**(-n))
        if self.lo<0:raise ValueError('power requires nonnegative base here')
        return I(self.lo**n,self.hi**n)
def iv(v):return v if isinstance(v,I)else I(v)
def arctan(q,n):
    q=Q(q);s=sum(((-1)**k*q**(2*k+1)/Q(2*k+1)for k in range(n)),Q(0))
    r=(-1)**n*q**(2*n+1)/Q(2*n+1);return I(min(s,s+r),max(s,s+r))
PI=16*arctan(Q(1,5),48)-4*arctan(Q(1,239),16)
def log_base(q):
    q=Q(q)
    if not 1<=q<=2:raise ValueError('log base domain')
    z=(q-1)/(q+1);n=110
    s=2*sum((z**(2*k+1)/Q(2*k+1)for k in range(n)),Q(0))
    return I(s,s+2*z**(2*n+1)/(Q(2*n+1)*(1-z*z)))
LOG2=log_base(2)
def logq(q):
    q=Q(q)
    if q<=0:raise ValueError('log domain')
    k=0
    while q>2:q/=2;k+=1
    while q<1:q*=2;k-=1
    return log_base(q)+k*LOG2
def log(v):
    v=iv(v);return I(logq(v.lo).lo,logq(v.hi).hi)
def expq(q):
    q=Q(q)
    if q<0:return 1/expq(-q)
    n=180
    if q>=n+2:raise ValueError('exp remainder ratio')
    t=Q(1);s=t
    for k in range(1,n+1):t*=q/k;s+=t
    tail=t*q/(n+1)/(1-q/(n+2));return I(s,s+tail)
def exp(v):
    v=iv(v);return I(expq(v.lo).lo,expq(v.hi).hi)
rows=[]
def check(name,v,lo=None,hi=None):
    v=iv(v)
    if lo is not None and not Q(lo)<v.lo:raise RuntimeError(name+' lower failure')
    if hi is not None and not v.hi<Q(hi):raise RuntimeError(name+' upper failure')
    rows.append({'name':name,'lower_decimal':format(float(v.lo),'.16g'),'upper_decimal':format(float(v.hi),'.16g'),
      'strict_lower_threshold':None if lo is None else str(lo),'strict_upper_threshold':None if hi is None else str(hi),
      'exact_lower':str(v.lo),'exact_upper':str(v.hi)})
a=1/(8*PI);L=I(34);k=log(10/PI);v=log(L)-k
def A(t):
    u=t/2-log(t)+k
    return Q('.158')*t+(u*u-u/3)/(2*PI)
def F1(t):return a*t*t-(t/(2*PI)+Q('1.465'))*log(t)+Q('1.2325')*t
def F2(t):return a*t*(t-log(t))
check('pi',PI,'3.141592',Q(22,7));check('log10_over_pi',k,'1.15','1.16');check('log34',log(34),'3.52','3.53')
check('variable_height_at34',20*exp(17)/34,10**7)
check('center_coefficient',(PI*(1+Q(1,10**7-1))+PI*PI/10**7)/20,None,'.158')
check('A_at34',A(L));check('correct_LN11_at34',F1(L));check('LN12_at34',F2(L))
def CH93(t):
    z=t-2*log(t/(PI*exp(1)))
    return (z*z-4)/(8*PI)
check('source_CH2_93_minus_A_at34',CH93(L)-A(L),None,'-.003')
check('source_CH2_93_minus_A_at40',CH93(I(40))-A(I(40)),'.09')
check('misquoted_LN11_at34',a*L*L-L/(2*PI)+Q('1.465')*log(L)+Q('1.2325'))
# Uniform ray lower bounds: log(L)/L,v/L,v^2/L decrease for L>=34.
c=Q('1.2325')-Q('.158')-Q('1.16')/(2*Q('3.14'))+1/(12*Q(22,7))
check('uniform_F1_minus_A_per_L',c-Q('1.465')*Q('3.53')/34-(Q('2.38')**2+Q('2.38')/3)/(2*Q('3.14')*34),'.73')
br=3*Q('3.52')-4*Q('1.16')+Q(2,3)-8*Q(22,7)*Q('.158')
cost=(4*Q('2.38')**2+Q(4,3)*Q('2.38'))/34
check('uniform_F2_minus_A_per_L_scaled',br-cost,'1.8')
check('uniform_F2_minus_A_absolute_gain',Q('1.8')*34/(8*Q(22,7)),'2.4')
check('psi_theta_pi_transfer_price',Q('.821')+Q('1.10')+Q('.278')/34+14*34*exp(-17),None,'2.4')
check('LN11_minus_LN12_at30369.581',F1(I('30369.581'))-F2(I('30369.581')),0)
check('LN11_minus_LN12_at30369.582',F1(I('30369.582'))-F2(I('30369.582')),None,0)
check('false_global_order_trigger_L1e6',F1(I(10**6))-F2(I(10**6)),None,-400000)
check('two_range_low_sum_cap',Q('8.066')**2/(2*Q('3.141592'))+7/(8*Q('3.141592'))+Q(2,280)*(Q(6,5)+Q(6,5))-Q(2,5*20000),None,'10.651')
check('two_range_additive_price',Q('10.651')-Q('10.3194'),None,'.332')
check('PNT_primitive_anchor_constant',Q('1.94')*exp(4)/8+Q('.0462')*exp(4)/64+Q(2)*Q('1.838')/64+Q(5)*Q('1.838')/32,None,14)
check('J_square_pi_error',a*17**2*exp(Q(-17,2)),None,'.003')
p3=1+Q(1,17)+Q(2,17**2)+Q(6,17**3)
check('J_square_upper',p3+Q(72,17**4)+a*17**2*exp(Q(-17,2)),None,'1.071')
check('J_higher_powers',2*(exp(Q(-34,6))+34/LOG2*exp(Q(-34,4))),None,'.028')
check('weighted_T0_primitive',5*Q('.0462')+3*Q('1.838')*exp(-17),None,'.232')
check('weighted_T1_primitive',Q('.0462')*(5+Q(7,34)+Q(4,34**2))+Q('1.838')*exp(-17)*(3+Q(4,34)+Q(2,34**2)),None,'.241')
check('weighted_T0_spectral',Q('.047')+2*exp(-17),None,'.048')
check('weighted_T1_spectral',Q('.047')*(1+Q(1,34))+2*exp(-17),None,'.049')
check('prime_log_square_error',a*exp(Q(-17,2))*(Q(7,3)*17**2+Q(16,9)*17+Q(32,27)),None,'.01')
check('product_square_error',a*34/2*(exp(Q(-17,2))*(Q(7,3)*17+Q(8,9))+34*exp(-34)),None,'.006')
check('product_square_lower',1-Q(2,34)-exp(-17)/2-Q('.006'),'.935')
check('product_higher_power_allowance',34*exp(Q(-34,6)),None,'.118')
check('prime_log_higher_power_allowance',10*exp(Q(-34,6)),None,'.035')
check('M2_outside_prime_allowance',34*exp(-17),None,'.001')
check('absolute_M1_factor',1+Q('1.29')/(a*34**2),None,'1.04')
check('absolute_M2_factor',1+Q('1.40')/(a*34**2),None,'1.04')
check('absolute_product_factor',Q('1.001')*(1+Q('1.39')/(a*34**2)),None,'1.05')
check('absolute_log_product_size',(a*34+Q('1.39')/34)*exp(-17),None,'.000002')
check('Euler_gamma_upper',sum((Q(1,j)for j in range(1,1001)),Q(0))-log(1000),None,'.578')
check('log4pi_lower',log(4*PI),'2.531')
check('DGM_leading_constant',4-log(3*PI*PI),None,'.62')
check('DGM_secondary', (4+2*PI)/40,None,'.258')
check('DGM_cubes',3*exp(Q(-40,6)),None,'.004')
check('DGM_h_factor',(40**2+8)*3*40*exp(-20),None,'.001')
check('DGM_log_endpoint',6*40*exp(-20),None,'.00001')
check('CMS_Delta',Q('4.4')*43/(4*PI*2*10**9),None,'1e-8')
check('CMS_root_a_s_squared',Q('4.4')**2*43**2/(4*10**9),None,'1e-5')
check('CMS_outside_remainder',Q(24,9)*Q('1e-5'),None,'.001')
check('CMS_prime_power_allowance',Q(68)*43**2/(2*10**9),None,'.001')
check('CMS_total_normalized_error',Q('.959')/Q('.83'),None,'1.16')
check('CMS_log_gain',log(Q('2.63')*Q('.69')*42/2),3)
result={'status':'PASS_EXACT_RATIONAL_SCALAR_CHECKS','optimization':sys.flags.optimize,'checks':len(rows),
 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'meaning':'Finite scalar checks with rational series error bounds; handwritten monotonicity and source theorems remain separately reviewed. Not kernel verification and not source-first PV.',
 'rows':rows}
dest=Path(sys.argv[1])if len(sys.argv)==2 else Path(__file__).with_name('SCALAR_CHECKS.json')
dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','optimization','checks','checker_sha256']}))
