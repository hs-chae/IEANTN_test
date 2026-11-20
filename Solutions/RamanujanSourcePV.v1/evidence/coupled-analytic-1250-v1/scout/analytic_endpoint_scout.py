#!/usr/bin/env python3
"""Exact integer interval scout; not a Lean proof or source-first PV.

All intervals have denominator 2**160. The mathematical interpretation relies on
Taylor identities and their displayed geometric tail bounds, plus 0<=EulerGamma<=1.
No floating-point/transcendental library is used to compute acceptance intervals.
"""
from dataclasses import dataclass
from math import factorial, isqrt
from decimal import Decimal, localcontext
from pathlib import Path
from hashlib import sha256
import json

BITS = 160
SCALE = 1 << BITS
LOG_TERMS = 128
EI_TERMS = 200
EXP_TERMS = 128

def ceildiv(a, b):
    return -((-a) // b)

@dataclass(frozen=True)
class I:
    lo: int
    hi: int
    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('unordered interval')
    @staticmethod
    def rat(a, b=1):
        if b <= 0:
            raise ValueError('nonpositive denominator')
        return I(a*SCALE//b, ceildiv(a*SCALE,b))
    def __add__(self, b):
        return I(self.lo+b.lo, self.hi+b.hi)
    def __neg__(self):
        return I(-self.hi,-self.lo)
    def __sub__(self,b):
        return self+-b
    def __mul__(self,b):
        xs=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(xs)//SCALE,ceildiv(max(xs),SCALE))
    def __truediv__(self,b):
        if b.lo<=0:
            raise ValueError('division denominator not positive')
        pairs=[(x*SCALE,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(a//d for a,d in pairs),max(ceildiv(a,d) for a,d in pairs))
    def sqrt(self):
        if self.lo<0:
            raise ValueError('sqrt negative endpoint')
        lower=isqrt(self.lo*SCALE)
        high=isqrt(self.hi*SCALE)
        if high*high!=self.hi*SCALE:
            high+=1
        return I(lower,high)
    def receipt(self):
        with localcontext() as c:
            c.prec=55
            a=str(Decimal(self.lo)/Decimal(SCALE));b=str(Decimal(self.hi)/Decimal(SCALE))
        return {'scaled_lower':str(self.lo),'scaled_upper':str(self.hi),'denominator':str(SCALE),'decimal_display':[a,b]}

ZERO=I.rat(0);ONE=I.rat(1);TWO=I.rat(2)

def log_series(q):
    if q.lo<0 or q.hi>=SCALE:
        raise ValueError('atanh series range')
    q2=q*q
    power=q
    total=ZERO
    for j in range(LOG_TERMS):
        total=total+power/I.rat(2*j+1)
        power=power*q2
    tail=TWO*power/I.rat(2*LOG_TERMS+1)/(ONE-q2)
    return TWO*total+I(0,tail.hi)

LN2=log_series(I.rat(1,3))

def log_point(a):
    if a<=0:
        raise ValueError('log input nonpositive')
    k=a.bit_length()-SCALE.bit_length()
    if k>=0:
        while a<SCALE*(1<<k):k-=1
        while a>=SCALE*(1<<(k+1)):k+=1
    else:
        while a*(1<<(-k))<SCALE:k-=1
        while a*(1<<(-(k+1)))>=SCALE:k+=1
    y=I.rat(a,SCALE*(1<<k)) if k>=0 else I.rat(a*(1<<(-k)),SCALE)
    q=(y-ONE)/(y+ONE)
    return LN2*I.rat(k)+log_series(q)

def log(x):
    a=log_point(x.lo);b=log_point(x.hi)
    return I(a.lo,b.hi)

def exp_one():
    total=ZERO
    for j in range(EXP_TERMS+1):
        total=total+I.rat(1,factorial(j))
    tail=I.rat(1,factorial(EXP_TERMS+1))/(ONE-I.rat(1,EXP_TERMS+2))
    return total+I(0,tail.hi)

E=exp_one()

def ei_without_gamma(z):
    if z.lo<=0 or z.hi>=45*SCALE:
        raise ValueError('Ei series range requires 0<z<45')
    term=z
    total=ZERO
    for k in range(1,EI_TERMS+1):
        total=total+term
        term=term*z*I.rat(k)/I.rat((k+1)**2)
    # After iteration200, term encloses z^201/(201*201!).
    ratio=I(0,z.hi)/I.rat(EI_TERMS+2)
    tail=term/(ONE-ratio)
    return log(z)+total+I(0,tail.hi)

def li(x):
    # Euler's gamma belongs to[0,1]. Deliberate width1 avoids oracle constants.
    return ei_without_gamma(log(x))+I(0,SCALE)

def source_envelope(x,c):
    L=log(x)
    return ei_without_gamma(L-ONE)+I(0,SCALE)-c*(x/E).sqrt()/(L-ONE)-li(x)*li(x)*L/(E*x)

def evolved_envelope(x,c):
    L=log(x)
    # The gamma terms cancel in li(x)+2/log2-li2.
    upper=ei_without_gamma(L)-ei_without_gamma(LN2)+TWO/LN2-I.rat(1,20)*x.sqrt()/L
    return ei_without_gamma(L-ONE)+I(0,SCALE)-c*(x/E).sqrt()/(L-ONE)-upper*upper*L/(E*x)

def run():
    outputs={
      'C0_positive':TWO/LN2-li(I.rat(2)),
      'x_over_e_domain_slack_at_1490b':I.rat(1490000000000)-E*I.rat(500000000000),
      'D_derivative_dominance_at_1490b':I.rat(1490000000000)*(log(I.rat(1490000000000))-I.rat(4))/(log(I.rat(1490000000000))*(log(I.rat(1490000000000))-TWO))-(TWO/LN2-li(I.rat(2))),
      'axler_original_endpoint':source_envelope(I.rat(1620000000000),I.rat(5301,2500)),
      'evolved_1500b_endpoint':evolved_envelope(I.rat(1500000000000),I.rat(1061,500)),
      'evolved_1490b_endpoint':evolved_envelope(I.rat(1490000000000),I.rat(1061,500)),
      'buthe_coefficient_at_500b_slack':I.rat(1061,500)-(I.rat(39,20)+I.rat(39,10)/log(I.rat(500000000000))+I.rat(39,2)/(log(I.rat(500000000000))*log(I.rat(500000000000)))),
      'li_upper_bound_base_at_exp4':(E*E*E*E)/TWO-li(E*E*E*E),
      'derivative_sufficient_at_1060b':I.rat(1060000000000).sqrt()-I.rat(1061,1000)*E.sqrt()*log(I.rat(1060000000000))*log(I.rat(1060000000000))*log(I.rat(1060000000000))*log(I.rat(1060000000000)),
    }
    for key,value in outputs.items():
        if value.lo<=0:
            raise RuntimeError(f'positive-bound check failed:{key}')
    return {'status':'Exact-integer outward-rounded endpoint scout passed; not source-first PV or Lean formalization.','bits':BITS,'log_terms':LOG_TERMS,'ei_terms':EI_TERMS,'exp_terms':EXP_TERMS,'analytic_premises':['Ei(logx) identity with gamma in[0,1]','atanh positive series and geometric remainder','Ei positive series and geometric remainder','factorial exp1 series and geometric remainder','Büthe2017finalTheorem2 and explicitly recorded partial-summation/derivative proof'],'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'outputs':{k:v.receipt() for k,v in outputs.items()}}

if __name__=='__main__':
    result=run()
    target=Path(__file__).with_name('analytic_endpoint_scout_receipt.json')
    temporary=target.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(result,indent=2)+'\n')
    temporary.replace(target)
    for key,row in result['outputs'].items():
        print(key,*row['decimal_display'])
