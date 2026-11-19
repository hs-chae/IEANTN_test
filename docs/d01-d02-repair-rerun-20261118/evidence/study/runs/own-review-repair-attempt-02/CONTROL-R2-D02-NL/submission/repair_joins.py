"""Check that both real closed finite sweeps meet the analytic tail."""
from repair_spectral import *
from repair_finite import LIMIT,START,STRIDE,Cs
from finite_joins import nxt
from pathlib import Path
import re

def joins():
    txt=Path(__file__).with_name('repair_finite_run.txt').read_text().splitlines()
    # The finite scan has exactly one obstruction row per target;
    # all these joins precede the old shared finite endpoint.
    rows=[]
    for c,line in zip(Cs,txt[1:1+len(Cs)]):
        s,*xs=line.split()
        assert D(s)==c and len(xs)==4
        xs=list(map(int,xs))
        assert all(START<=x<LIMIT and (x-START)%STRIDE==0 for x in xs)
        rows.append((str(c),xs))
    assert len(rows)==len(Cs)
    finite_tail()
    old=Path(__file__).with_name('finite_run.txt').read_text()
    for c,indices in [('0.11',(3,)),('0.1',range(4))]:
        a=re.search(r'^'+re.escape(c)+r' \[([^\]]+)\]$',old,re.M)
        xs=list(map(int,a.group(1).split(', ')))
        for i in indices:
            on=nxt(xs[i])
            assert on<25000000 and dict(rows)[str(D(c) if c!='0.1' else D('0.10'))][i]<=25000000
            print('old obstruction now joined',c,i+1,on)

def jump():
    u=I(32)
    dlt=(I('.5')-11)*u*ef(1,u)+(12-I(16)/5)*fact[21]/u**21
    assert D('6.8283e-12')<dlt.l and dlt.r<D('6.8284e-12')
    print('left minus right R2 remainder at L=32',dlt)

if __name__=='__main__':
    jump()
    joins()
