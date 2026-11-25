#!/usr/bin/env python3
"""Reproduce the exact basis conversion and independently check the Fourier polynomial.

Finite Fraction computation, not a Lean proof or source-first PV. No randomness.
The output directory must be fresh. Published input files are never changed.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'primal40'))
from generate_kernel_cells import laguerre_polynomials,source_polynomials

def need(c,message):
 if not c:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();here=Path(__file__).resolve().parent
 need(not a.out.exists(),'Fresh output directory required')
 original=here/'OPT28_ORIGINAL.json';fixed=here/'CANDIDATE_LAGUERRE28.json';expected=json.loads(fixed.read_text())
 need(sha(original)==expected['source_file_sha256'],'Original timely input SHA mismatch')
 raw=json.loads(original.read_text());need(set(raw)=={'polynomial_in_y_squared','searched_ratio','target'},'Unexpected original schema')
 need(len(raw['polynomial_in_y_squared'])==29 and all(isinstance(x,str)for x in raw['polynomial_in_y_squared']),'Expected29 exact rational strings')
 p=list(map(Q,raw['polynomial_in_y_squared']));basis=laguerre_polynomials(28);residual=p.copy();c=[Q(0)]*29
 for j in reversed(range(29)):
  c[j]=residual[j]/basis[j][j]
  for k in range(j+1):residual[k]-=c[j]*basis[j][k]
 need(not any(residual),'Nonzero exact basis-conversion residual')
 packet={'degree':28,'coefficients_decimal_exact_rationals':list(map(str,c)),'source':'prospective frozen E2 timely token prefix; exact rational basis conversion only','source_file_sha256':sha(original),'physical_degree':56}
 # Historical metadata spelling is preserved byte-for-byte as part of identity.
 packet['source']=expected['source']
 encoded=json.dumps(packet,indent=2)+'\n';need(encoded.encode()==fixed.read_bytes(),'Reconstructed candidate bytes differ')
 P,G=source_polynomials(packet);need(P[::2]==p and not any(P[1::2]),'Actual physical P differs from timely input')
 transformed=[Q(0)]*57;monomial=[Q(1)]
 for n in range(57):
  if n%2==0:
   for k,v in enumerate(monomial):transformed[k]+=(-1)**(n//2)*P[n]*v
  following=[Q(0)]*(len(monomial)+1)
  for k,v in enumerate(monomial):
   if k:following[k-1]+=Q(k,2)*v
   following[k+1]-=v
  monomial=following
 need(transformed==G,'Independent monomial/Hermite Fourier transform differs')
 a.out.mkdir(parents=True);(a.out/'CANDIDATE_LAGUERRE28.json').write_text(encoded)
 receipt={'status':'PASS_EXACT_TIMELY_MONOMIAL_LAGUERRE_PHYSICAL_AND_INDEPENDENT_HERMITE_ASSOCIATION','scope':'Exact Fraction reconstruction, not Lean or source-first PV','original_sha256':sha(original),'candidate_sha256':sha(fixed),'coefficients':29,'physical_degree':56,'recovery_source_sha256':sha(Path(__file__)),'Python':sys.version,'seed':None}
 (a.out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status'])
if __name__=='__main__':main()
