"""Reproduce selected failed sufficient tests, not counterexamples."""
from verify02 import *
for onset,d in [('185.5',2),('210',3),('235.5',4)]:
    L=I(onset);c=P(d)
    v=sum((a-(c[j] if j<len(c) else 0))/L**j for j,a in enumerate(r.CO[4:]))-r.loss(L,lambda u:pi_bound(u,1))
    assert low(0,v)
    print('Negative B0 sufficient test at new D02 onset',onset,d,v,flush=True)
for B,d in [(185,2),(209,3),(235,4)]:
    L=I(B); c=P(d)
    v=sum((a-(c[j] if j<len(c) else 0))/L**j for j,a in enumerate(r.CO[4:]))-r.loss(L,lambda u:pi_bound(u,0))
    assert low(0,v)
    print('Negative D02 sufficient test for an earlier attempt',B,d,v,flush=True)
for c,b,z in [('.261',173,0),('.01495',193,1)]:
    try:finite_m(c,13,b,z)
    except ValueError as e:print('Failed finite sufficient test',c,z,e,flush=True)
    else:raise RuntimeError('Expected negative result changed; inspect for a better bound')
