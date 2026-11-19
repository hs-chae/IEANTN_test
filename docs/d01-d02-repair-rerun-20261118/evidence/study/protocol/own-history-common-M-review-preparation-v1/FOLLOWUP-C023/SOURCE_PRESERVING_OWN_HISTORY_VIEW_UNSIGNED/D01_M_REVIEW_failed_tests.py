"""Deterministic reproduction of failed sufficient checks, not function counterexamples."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path.cwd()))
from ram_repair import Q,adapt
from m_postreview import ray,power_coef
a=Q(250);v=power_coef(a)
assert v>Q('.01606')
print('insufficient power coefficient', a,float(v))
for A,B,j,z in [('47.65',191,6,'8.36'),('50.1',157,6,105)]:
    a,n,u,v=adapt(A,B,j,z)
    assert a<=0
    print('insufficient cell',A,B,j,z,str(u),str(v),float(a))
for L,k in [('38.1','.00002'),('64','4.3e-8')]:
    try: ray(Q(L),Q(k),True)
    except AssertionError as e:print('insufficient logarithmic ray',L,k,str(e))
    else:raise AssertionError('expected failed sufficient test')
