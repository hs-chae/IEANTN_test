#!/usr/bin/env python3
"""Exact-rational Gaussian cell certificate EXPLORATION; not a Lean acceptance receipt."""
import argparse,json,math,time,hashlib
from fractions import Fraction as F
from pathlib import Path

def add(p,q):
 r=[F(0)]*max(len(p),len(q))
 for i,x in enumerate(p):r[i]+=x
 for i,x in enumerate(q):r[i]+=x
 return r

def scale(p,c):return [x*c for x in p]
def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):r[i+j]+=x*y
 return r

def shift(p,a,h):
 r=[F(0)]*len(p)
 for i,x in enumerate(p):
  for j in range(i+1):r[j]+=x*math.comb(i,j)*a**(i-j)*h**j
 return r

def ceil_dyadic(x,bits=256):
 den=1<<bits
 return F(-((-x.numerator*den)//x.denominator),den)

def exp_upper_neg(z):
 # z <= 0; exp(z)=exp(z/2^k)^(2^k), |z/2^k|<=1.
 # Lagrange remainder about0 onnegativeaxis bounded by |z/2^k|^24/24!.
 if z>0:raise ValueError('requires nonpositive argument')
 m=1
 while -z>m:m*=2
 q=z/m
 t=sum((q**j/F(math.factorial(j)) for j in range(24)),F(0))+q**24/F(math.factorial(24))
 t=ceil_dyadic(t)
 while m>1:
  t=ceil_dyadic(t*t);m//=2
 return t

def cell(p,a,b,n,kind):
 h=b-a; pp=shift(p,a,h)
 lo=pp[0]+sum((x for x in pp[1:] if x<0),F(0)); hi=pp[0]+sum((x for x in pp[1:] if x>0),F(0))
 if lo>=0:AA=pp;sgn=1
 elif hi<=0:AA=scale(pp,-1) if kind=='abs' else [F(0)];sgn=-1
 else:AA=[max(-lo,hi)];sgn=0
 M=sum(abs(x) for x in AA)
 delta=[F(0),2*a*h,h*h]
 tt=[F(0)]; power=[F(1)]
 for j in range(n):
  tt=add(tt,scale(power,F((-1)**j,math.factorial(j))))
  power=mul(power,delta)
 product=mul(AA,tt)
 I=sum((x/F(i+1) for i,x in enumerate(product)),F(0))
 rr=M*(b*b-a*a)**n/F(math.factorial(n))
 upper=ceil_dyadic(h*exp_upper_neg(-a*a)*(max(F(0),I)+rr),80)
 return {'a':a,'b':b,'lo':lo,'hi':hi,'sgn':sgn,'I':I,'M':M,'remainder':rr,'upper':upper,'terms':len(product)}

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,list):return [encode(z) for z in x]
 if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input');ap.add_argument('--candidate');ap.add_argument('--out',required=True);ap.add_argument('--denom',type=int,default=32);ap.add_argument('--root-denom',type=int,default=16384);ap.add_argument('--terms',type=int,default=8);args=ap.parse_args()
 if bool(args.input)==bool(args.candidate):raise ValueError('Provide exactly one of --input and --candidate')
 packet=json.load(open(args.input)) if args.input else None
 if args.candidate:
  from generate_kernel_cells import source_polynomials
  norm,wing=source_polynomials(json.load(open(args.candidate)))
 else:
  norm=[F(x) for x in packet['P']['polynomial_low_to_high_coeffs']]
  wing=[F(x) for x in packet['Q']['polynomial_low_to_high_coeffs']]
 def square_arg(p):
  r=[F(0)]*(2*len(p)-1)
  for i,x in enumerate(p):r[2*i]=x
  return r
 if not args.candidate:norm=square_arg(norm);wing=square_arg(wing)
 result={};start=time.monotonic()
 for name,p,left,kind in [('norm',norm,F(0),'abs'),('wing',wing,F(1772453850905,10**12),'positive')]:
  cells=[]
  def refine(a,b):
   c=cell(p,a,b,args.terms,kind)
   if c['sgn']==0 and b-a>F(1,args.root_denom):
    mid=(a+b)/2;refine(a,mid);refine(mid,b)
   else:cells.append(c)
  a=left
  while a<12:
   b=min(F(12),a+F(1,args.denom));refine(a,b);a=b
  total=sum((c['upper'] for c in cells),F(0))
  # 2/sqrt(pi) <= 1.12838 verified separately in planned Lean bridge.
  normbound=F(1128379167096,10**12)*total
  result[name]={'cells':cells,'raw_half_integral_upper':total,'scaled_finite_upper':normbound,'scaled_finite_upper_float':float(normbound),'sign_uncertain_cells':sum(c['sgn']==0 for c in cells)}
  print(name,len(cells),float(normbound),'sec',time.monotonic()-start,flush=True)
 result['parameters']={'terms':args.terms,'root_denom':args.root_denom,'denom':args.denom,'cutoff':12,'sqrtpi_wing_lower':str(F(1772453850905,10**12)),'two_over_sqrtpi_upper':str(F(1128379167096,10**12))}
 result['status']='EXPLORATORY_EXACT_RATIONAL_FINITE_BOUNDS_NOT_LEAN_VERIFIED_NO_TAIL_OR_SCALING_PROOF'
 Path(args.out).write_text(json.dumps(encode(result),indent=2)+'\n')
 print('output',args.out,'bytes',Path(args.out).stat().st_size,flush=True)
if __name__=='__main__':main()
