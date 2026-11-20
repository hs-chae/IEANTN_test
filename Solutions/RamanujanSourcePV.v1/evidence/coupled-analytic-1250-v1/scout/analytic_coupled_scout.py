#!/usr/bin/env python3
"""NEW bounded analytic scout. Exact integer intervals, not Lean/PV acceptance.
Original source inputs and accepted 1.49T result are unchanged.
"""
from pathlib import Path
from hashlib import sha256
import json
from analytic_endpoint_scout import I,ONE,TWO,E,log,li

def power(x,n):
 out=ONE
 for _ in range(n):out=out*x
 return out

ANCHOR_SQRT=power(E,7)*E.sqrt()
K=I.rat(1561,12375)*ANCHOR_SQRT
D=I.rat(117,22)

def coupled(x,j=True):
 L=log(x);y=x/E;M=L-ONE;root=y.sqrt();U=K+D*root/(M*M)
 A=li(y)-I.rat(39,20)*root/M-U
 B=li(x)-I.rat(1,20)*x.sqrt()/L-U
 J=I.rat(1,10)*(x.sqrt()/(L*L)-root/(M*M))
 if j:B=B-J
 return A-B*B*L/(E*x)

def main():
 points=[10**12,1100000000000,1150000000000,1200000000000,1250000000000,1300000000000,1350000000000,1400000000000,1490000000000]
 rows=[]
 for n in points:
  result=coupled(I.rat(n));rows.append(dict(x=n,coupled_with_last_integral=result.receipt(),coupled_without_last_integral=coupled(I.rat(n),False).receipt()))
 lo=1100000000000;hi=1400000000000
 while hi-lo>1000000:
  mid=(lo+hi)//2
  if coupled(I.rat(mid)).lo>0:hi=mid
  else:lo=mid
 out=dict(status='EXACT_INTEGER_INTERVAL_SCOUT_NOT_LEAN_OR_SOURCE_FIRST_PV',unchanged_original_transition=1490000000000,base_script_sha256=sha256(Path(__file__).with_name('analytic_endpoint_scout.py').read_bytes()).hexdigest(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_additional_source_input='Buthe1511.02032v2 Theorem2 Eq1.6: t-theta(t)<=1.95sqrt(t),1423<=t<=1e19',same_other_analytic_inputs_preserved=True,anchor_log=15,Uerr_constant=K.receipt(),Uerr_sqrt_coefficient='117/22',normalized_envelope_rows=rows,positive_crossing_scout=dict(nonpositive_or_unproved_at=lo,strictly_positive_at=hi),global_monotonicity_not_yet_proved=True,no_original_array_or_result_changed=True)
 target=Path(__file__).with_name('analytic_coupled_scout_receipt.json');tmp=target.with_suffix('.pending');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(target)
 for row in rows:print(row['x'],row['coupled_with_last_integral']['decimal_display'])
 print('crossing',lo,hi)
if __name__=='__main__':main()
