"""Extract the certified sufficient joins from the finite sweep receipt."""
from decimal import Decimal
from pathlib import Path
from math import isqrt

def nxt(p):
    n=p+1
    while True:
        if n>=2 and all(n%d for d in range(2,isqrt(n)+1)): return n
        n+=1

if __name__=='__main__':
    data=Path(__file__).with_name('finite_run.txt').read_text()
    a=data.split('Last unproved endpoints (including one-sided prime limits)\n')[1].split('Endpoint maxima')[0]
    for s in a.splitlines():
        c,v=s.split(' [')
        v=[int(x) for x in v.rstrip(']').split(', ')]
        if Decimal(c)>=Decimal('.12'):
            print(c,[nxt(max(x,10000)) for x in v])
        if Decimal(c)==Decimal('.11'):
            print(c,[nxt(max(x,10000)) for x in v[:3]])
