#!/usr/bin/env python3
"""Independent exact-rational chord scout. Not a Lean theorem or source-first PV.

No FFT or floating trig evaluation. Machin arctangent intervals, rational cosine
Taylor evaluation with absolute remainder, and the conservative periodic chord
bound (80/(12G^2))*sum j^2 |w_j|. Final norm identity/chord lemmas remain formal
proof obligations until connected to the affine Fourier bridge.
"""
import argparse,hashlib,json,math,os,sys,time
from fractions import Fraction as Q
from pathlib import Path

def need(v,s):
 if not v:raise ValueError(s)
def arctan(q,n):
 z=Q(1,q);v=sum(((-1)**j*z**(2*j+1)/(2*j+1)for j in range(n)),Q(0));t=z**(2*n+1)/(2*n+1)
 return(v-t,v)if n%2 else(v,v+t)
def times(x,y):
 vals=[a*b for a in x for b in y];return min(vals),max(vals)
def cos_interval(k,G,pi,N=24):
 # Exact reduction to [-pi/2,pi/2], evenness, and cos(pi-y)=-cos(y).
 k%=G;k=min(k,G-k);sign=1
 if 4*k>G:k=G//2-k;sign=-1
 y=(2*Q(k,G)*pi[0],2*Q(k,G)*pi[1]);v=(Q(0),Q(0));y2=times(y,y)
 for j in reversed(range(N)):
  v=times(v,y2);c=Q((-1)**j,math.factorial(2*j));v=(v[0]+c,v[1]+c)
 rem=y[1]**(2*N)/math.factorial(2*N)
 v=(v[0]-rem,v[1]+rem)
 return v if sign==1 else(-v[1],-v[0])
def area(l,r):
 if l>=0 and r>=0:return(l+r)/2
 if l<=0 and r<=0:return Q(0)
 return max(l,r)**2/(2*abs(l-r))
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--grid',type=int,default=256);ap.add_argument('--A',default='4.00001');ap.add_argument('--alpha',default='1');ap.add_argument('--width',default='2.12');ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);began=time.monotonic();dat=json.loads(a.candidate.read_text());m=dat['m'];G=a.grid;need(G>=4 and G%4==0,'Grid divisible by4');w=[Q(z,dat['scale'])for z in dat['coefficients']]+[Q(0)]
 l5,u5=arctan(5,40);l239,u239=arctan(239,40);pi=(16*l5-4*u239,16*u5-4*l239);need(pi[1]**2<10,'pi squared below10')
 cs=[cos_interval(k,G,pi)for k in range(G)];values=[]
 for k in range(G):
  lo=hi=w[0]
  for j in range(1,len(w)):
   z=times((2*w[j],2*w[j]),cs[j*k%G]);lo+=z[0];hi+=z[1]
  values.append((lo,hi))
 # Store compact upward rounded dyadic samples and exact conservative chord.
 bits=80;unit=2**bits;ups=[-((-max(abs(l),abs(u))*unit).numerator//(-max(abs(l),abs(u))*unit).denominator)for l,u in values]
 sample=Q(sum(ups),G*unit);chord=Q(80,12*G*G)*sum((j*j*abs(z)for j,z in enumerate(w)),Q(0));N=sample+chord
 F0=(w[0]+2*sum(w[1:]))/m;J=2*sum((area(w[j],w[j+1])for j in range(m,len(w)-1)),Q(0))/m;M=max(map(abs,w));A=Q(a.A);alpha=Q(a.alpha);D=F0-A*J;width=Q(a.width)
 need(D>0,'Positive denominator');need((N+2*alpha*M)<width*D,'Proposed weighted width failed')
 result={'status':'PASS_EXACT_RATIONAL_CHORD_NUMERICS_NOT_LEAN_THEOREM_OR_PV','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'m':m,'node_count':len(w)-1,'grid':G,'A':str(A),'alpha':str(alpha),'width':str(width),'sample_dyadic_unit':str(unit),'sample_abs_upper_integers':ups,'scalars':{key:{'exact':str(z),'approx':float(z)}for key,z in [('N_upper',N),('sample_average_upper',sample),('chord_allowance',chord),('F0',F0),('J',J),('M',M),('D',D),('weighted_ratio_upper',(N+2*alpha*M)/D),('width_margin',width*D-(N+2*alpha*M))]},'pi_lower':str(pi[0]),'pi_upper':str(pi[1]),'cos_taylor_terms':24,'seconds':time.monotonic()-began,'python':sys.version,'command':sys.argv}
 (a.out/'CANDIDATE.json').write_bytes(a.candidate.read_bytes());p=a.out/'RESULT.json.tmp';p.write_text(json.dumps(result,indent=2)+'\n');os.link(p,a.out/'RESULT.json');p.unlink();print(json.dumps({key:result[key]for key in ['status','m','grid','width','seconds']}));print(json.dumps(result['scalars']))
if __name__=='__main__':main()
