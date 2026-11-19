from interval import *
from subprocess import run
import sys
a=38358837682
b=14111427770
for n in (a,a+1):
 z=I(n)/ex(1)
 assert b*S<z.a<=z.b<(b+1)*S
rows=run([sys.argv[1]],input=chr(10).join(map(str,(a,a+1,b)))+chr(10),text=True,check=True,capture_output=True).stdout
assert [tuple(map(int,z.split())) for z in rows.splitlines()]==[(a,1644673232),(a+1,1644673232),(b,632207037)]
def r(x):return ex(1)*I(x)*632207037/ln(x)-1644673232**2
assert r(a).b<0 and r(a+1).yes()
lo,hi=a*10**8,(a+1)*10**8
while hi-lo>1:
 m=(lo+hi)//2
 v=r(Fraction(m,10**8))
 if v.yes():hi=m
 else:assert v.b<0;lo=m
print(rows.strip());print("gap at a",r(a));print("gap at a+1",r(a+1));print("unique real zero between", lo, hi, "divided by 10^8")
