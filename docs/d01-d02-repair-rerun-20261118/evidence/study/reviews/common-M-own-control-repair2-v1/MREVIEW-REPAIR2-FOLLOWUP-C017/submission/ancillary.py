# Small checks of candidate obligations; not a new proof construction.
import sys, re, subprocess, os
from pathlib import Path
from zipfile import ZipFile
from hashlib import sha256
A=Path('/work/exact')
sys.path.insert(0,str(A))
from profiles import *
from repair_spectral import coeff as old_coeff
from log_layer import coeff as new_coeff, sec
from second_m import WIDER
from repair_evaluate import r_augment
from mertens import prime_powers
from finite_joins import nxt

# Original log/medium product formula includes the entire denominator.
for b,C in [(basecap,D('.006665')),(newcap,D('.11625'))]:
    value=(old_coeff(b)[1]+21/I(H)).r
    assert value<C
    print('old secant with limiting allowance',b,value,C)

# Declared comparison barriers are for estimates, not the numbers being estimated.
C=I('1.044e-12')
floor=PI/I(3000175332800)
for T in (I('166.1'),I(168)):
    # Biggest small prime-power/log conversion perturbations used in the comparison.
    pp=3*ef(I('.5'),T)+2*ef(1,T)/T
    L=(floor-pp)
    assert (L-L*L/(2*T)).l>C.r
    print('endpoint barrier after prime-power and exp conversion',T,L)
assert (I('.22775')*ef(I(1)/32,I(168))).r<D('.0016')
for rad in ('167','168','170'):
    u=I(rad)
    # On these log domains the old step bound's last coefficient can come
    # from D or A_h; check A_h at the larger splitting width as well.
    A0=2/(H*I('2.1e-12'))
    assert (A0*(ell+1)/3).l>D('.0017')

# Explicit fixed example of the *historical* bad x-mode path.
from zipfile import ZipFile
with ZipFile(A/'before_own_repair.zip') as z:
    data=z.read('repair_evaluate.py')
print('historical evaluator SHA256',sha256(data).hexdigest())
c=[sys.executable,'-c',
   'import sys,os,zipfile; f=os.path.join(os.getcwd(),"repair_evaluate.py"); '
   'src=zipfile.ZipFile("before_own_repair.zip").read("repair_evaluate.py"); '
   'sys.argv=[f,"x","1e70"]; exec(compile(src,f,"exec"),{"__file__":f,"__name__":"__main__"})']
old=subprocess.run(c,cwd=A,check=True,capture_output=True,text=True)
print('old stdout:')
print(old.stdout,end='')
print('old stderr:',repr(old.stderr))
vv=[D(x) for x in re.findall(r'R lower endpoint in x\^2/L\^6 units (\S+)',old.stdout)]
assert len(vv)==2 and min(vv)>D('737000000')
u=I('1e70').ln()
def F(v):return v*ef(1,v)*vintegral(v)
for b in (basecap,newcap):
    up,_=p_err(u-1,b); _,dn=p_err(u,b)
    upper=u**4*(u/(u-1)*(F(u-1)+up)-maxi(0,F(u)-dn)**2)
    assert r_augment(u,b).l>D('1.09') and upper.r<D('1.1')
    print('reversed brackets upper',b,upper.r)
