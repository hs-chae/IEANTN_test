"""Regression: original failing x-mode, both caps and both slice sizes."""
from repair_evaluate import *
from subprocess import run
from sys import executable

def run_x(x):
    return run([executable,'-B',str(PTH/'repair_evaluate.py'),'x',x],
        cwd=PTH,capture_output=True,text=True,check=True,timeout=180).stdout

text=run_x('1e70')
reported=[D(s.split()[-1]) for s in text.splitlines() if s.startswith('R lower')]
assert len(reported)==2
u=I('1e70').ln()
assert u.r>u.l>141
# Opposite enclosure using the unmodified original pi bounds, not the
# extrapolation from a log point or the procedure that computes the lower.
def norm(v):return v*ef(1,v)*vintegral(v)
for cap,w in zip((basecap,newcap),reported):
    _,dn=p_err(u,cap)
    up1,_=p_err(u-1,cap)
    upper=u**4*(u/(u-1)*(norm(u-1)+up1)-maxi(0,norm(u)-dn)**2)
    assert D('1.09')<w<=upper.r<D('1.1')
    for hi in (False,True):
        full=POS if hi else dNplus
        for k in (4,6,20):
            # Independent full Horner and term subtraction in unscaled units.
            ds=[0]*k+full[k:]
            ref=u**k*(horner(ds,1/u)-cost(u,cap,hi))
            check=margin_interval(u,cap,k,hi)
            assert max(ref.l,check.l)<=min(ref.r,check.r)
    print('cap',cap,'actual x-mode lower',w,'independent upper',upper.r)
for s in ('1.5','2'):
    out=run_x(s)
    assert out.count('M upper endpoints')==2 and 'R lower' not in out
    print(s,'both finite M paths ran')
