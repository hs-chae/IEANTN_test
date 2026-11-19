"""Additive certified rows; this parser is not their mathematical proof."""
from pathlib import Path
from second_m import TABLE
from second_finite import START,LIMIT,STRIDE,Cs
import json

P=Path(__file__).resolve().parent
def lines(f):
    return (P/f).read_text().splitlines()
def main():
    levels=[]
    full={}
    for s in lines('second_r_run.txt'):
        if s.startswith('full '):
            _,k,m,b,c=s.split()
            k,m=int(k),int(m)
            full[k]=m
            levels.extend([[k,m,b,700],[k,m,c,675]])
        if s.startswith('fixed '):
            _,L,k,cap,m=s.split()
            levels.append([int(k),int(m),L,int(cap)])
    assert sorted(full)==list(range(6,63))
    for s in lines('compact_r_run.txt'):
        kind,r,k,cap,L,r2=(*s.split(),None)[:6]
        if kind=='full':
            assert r=='compact' and r2 is not None
            levels.append([int(k),full[int(k)],L,int(cap)])
        else:
            assert kind=='fixed' and r=='compact'
            u,k,cap,m=k,cap,L,r2
            levels.append([int(k),int(m),u,int(cap)])
    f=lines('second_finite_run.txt')
    assert int(f[0].split()[0])==LIMIT
    finite=[]
    for C,s in zip(Cs,f[1:]):
        c,*Ls=s.split()
        ns=list(map(int,Ls))
        assert str(C)==c and len(ns)==4 and all(START<=x<LIMIT and (x-START)%STRIDE==0 for x in ns)
        finite.append([c,*ns])
    assert len(finite)==len(Cs)
    a=[[17,'.01239',700],[17,'.22775',675],[190,'.2200',675],
       [200,'.01218',700],[200,'.21150',675]]
    for L,b,c in TABLE:a.extend([[L,b,700],[L,c,675]])
    pre=[]
    for s in lines('power_prefix_monotone_run.txt')[1:]:
        cap,c,*xs=s.split()
        b=int(cap)
        assert [17,c,b] in a and len(xs)==4
        on=list(map(int,xs))
        assert all(2<=v<500000 for v in on)
        pre.append([b,c,*on])
    assert len(pre)==2
    print(json.dumps(dict(R_uniform=levels,M_power=a,M_finite=finite,M_power_prefix=pre),indent=2))

if __name__=='__main__': main()
