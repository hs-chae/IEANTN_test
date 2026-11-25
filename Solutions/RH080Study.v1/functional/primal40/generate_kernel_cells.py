#!/usr/bin/env python3
"""Deterministically regenerate exact-rational Gaussian certificates; Lean alone accepts them."""
import argparse,json,math,time,hashlib
from fractions import Fraction as F
from pathlib import Path
from prototype_cells import ceil_dyadic

def add(p,q):return [(p[i] if i<len(p) else F(0))+(q[i] if i<len(q) else F(0)) for i in range(max(len(p),len(q)))]
def scale(a,p):return [a*c for c in p]
def mul(p,q):
 if not p:return []
 return add(scale(p[0],q),[F(0)]+mul(p[1:],q))
def power(p,n):return [F(1)] if n==0 else mul(p,power(p,n-1))
def comp(p,q):return [] if not p else add([p[0]],mul(q,comp(p[1:],q)))
def lower(p):return F(0) if not p else p[0]+min(F(0),lower(p[1:]))
def upper(p):return F(0) if not p else p[0]+max(F(0),upper(p[1:]))
def majorant(abs_mode,p):
 if lower(p)>=0:return p
 if upper(p)<=0:return scale(F(-1),p) if abs_mode else []
 return [max(-lower(p),upper(p))]
def taylor(a,h,n):
 out=[]
 for i in reversed(range(n)):out=add(scale(F((-1)**i,math.factorial(i)),power([F(0),2*a*h,h*h],i)),out)
 return out

def laguerre_polynomials(n):
 # L_j^{-1/2}(2v), exact recurrence.
 polys=[[F(1)]]
 if n:polys.append([F(1,2),F(-2)])
 for j in range(1,n):
  polys.append(scale(F(1,j+1),add(mul([F(2*j)+F(1,2),F(-2)],polys[j]),scale(-(F(j)-F(1,2)),polys[j-1]))))
 return polys

def source_polynomials(candidate):
 cs=[F(s) for s in candidate['coefficients_decimal_exact_rationals']]
 ls=laguerre_polynomials(len(cs)-1);p=[];q=[]
 for n,c in enumerate(cs):
  p=add(p,scale(c,ls[n]));q=add(q,scale((-1)**n*c,ls[n]))
 def square_arg(p):
  out=[F(0)]*(2*len(p)-1)
  for i,c in enumerate(p):out[2*i]=c
  return out
 return square_arg(p),square_arg(q)

def data_for(source,abs_mode,a,h):
 shifted=comp(source,[a,h]);maj=majorant(abs_mode,shifted);prod=mul(maj,taylor(a,h,8));M=sum(map(abs,maj),F(0));I=sum((c/F(i+1) for i,c in enumerate(prod)),F(0));q=a*a;m=1
 while q>m:m*=2
 z=q/m;B=ceil_dyadic(sum(((-z)**i/F(math.factorial(i)) for i in range(24)),F(0))+z**24/F(math.factorial(24)))
 E=ceil_dyadic(B**m)
 U=ceil_dyadic(h*E*(max(F(0),I)+M*(2*a*h+h*h)**8/F(math.factorial(8))),80)
 return dict(a=a,h=h,B=B,E=E,M=M,I=I,upper=U,m=m,shifted=shifted,majorant=maj,product=prod)

def lit(q):return '('+str(q.numerator)+'/'+str(q.denominator)+' : ℚ)'
def llist(xs):return '['+','.join(map(lit,xs))+']'
def record(d):return '{\n'+',\n'.join('  '+k+' := '+(llist(v) if isinstance(v,list) else str(v) if isinstance(v,int) else lit(v)) for k,v in d.items())+'\n}'

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--candidate',required=True);ap.add_argument('--partition',required=True);ap.add_argument('--output',required=True);ap.add_argument('--sample',action='store_true');ap.add_argument('--chunk-size',type=int,default=72);args=ap.parse_args()
 candidate=json.load(open(args.candidate));packet=json.load(open(args.partition));p,q=source_polynomials(candidate);out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
 originals=['import GaussianCertificate','open scoped BigOperators Interval','open MeasureTheory Set Polynomial','namespace RHOnePrime.GaussianKernel','def normSource : List ℚ := '+llist(p),'def wingSource : List ℚ := '+llist(q),'end RHOnePrime.GaussianKernel']
 (out/'GaussianSources.lean').write_text('\n'.join(originals)+'\n')
 rows=[]
 for name,source,mode in [('norm',p,True),('wing',q,False)]:
  cells=packet[name]['cells']
  for i,c in enumerate(cells):
   if args.sample and i not in [0,1]:continue
   d=data_for(source,mode,F(c['a']),F(c['b'])-F(c['a']));rows.append((name,i,mode,d))
 print('rows',len(rows),flush=True)
 chunks=[]
 for start in range(0,len(rows),args.chunk_size):
  num=start//args.chunk_size;module='GaussianCells'+str(num).zfill(2)
  lines=['import GaussianSources','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','open scoped BigOperators Interval','open MeasureTheory Set Polynomial','namespace RHOnePrime.GaussianKernel']
  for name,i,mode,d in rows[start:start+args.chunk_size]:
   nm=name+str(i).zfill(3);src=name+'Source';md=str(mode).lower()
   lines+=['def '+nm+' : GaussianCellData := '+record(d),'theorem '+nm+'_valid : CellValid '+md+' '+src+' '+nm+' := by decide +kernel','theorem '+nm+'_bound : (∫ u in ('+nm+'.a : ℝ)..(('+nm+'.a+'+nm+'.h : ℚ) : ℝ), positivePartOrAbs '+md+' (coeffEval '+src+' u)*Real.exp (-(u^2))) ≤ ('+nm+'.upper : ℝ) := cellValid_integral_upper '+md+' '+src+' '+nm+' '+nm+'_valid','#print axioms '+nm+'_bound']
  lines+=['end RHOnePrime.GaussianKernel'];(out/(module+'.lean')).write_text('\n'.join(lines)+'\n');chunks.append(module)
 def enc(d):return {k:[str(z) for z in v] if isinstance(v,list) else str(v) if isinstance(v,F) else v for k,v in d.items()}
 result={'status':'GENERATED_NOT_LEAN_ACCEPTANCE','rows':len(rows),'chunks':chunks,'sources':{'norm':list(map(str,p)),'wing':list(map(str,q))},'cells':[{'family':name,'index':i,'abs_mode':mode,'data':enc(d)} for name,i,mode,d in rows],'totals':{name:str(sum((d['upper'] for nm,i,mode,d in rows if nm==name),F(0))) for name in ['norm','wing']}}
 (out/'CELL_DATA.json').write_text(json.dumps(result,indent=2)+'\n')
 print('totals', {k:float(F(v)) for k,v in result['totals'].items()},flush=True)
 print('chunks',chunks,flush=True)
if __name__=='__main__':main()
