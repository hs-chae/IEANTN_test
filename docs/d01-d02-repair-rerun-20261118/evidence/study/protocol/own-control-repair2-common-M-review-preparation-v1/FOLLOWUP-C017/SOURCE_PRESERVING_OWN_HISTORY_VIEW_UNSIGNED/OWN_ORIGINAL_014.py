from finite_mertens import sieve
from intervals import *
from pathlib import Path
import re

def normalizers():
    line=Path(__file__).with_name('finite_run.txt').read_text().splitlines()[1]
    return tuple(I(l,r) for l,r in re.findall(r'\[([\d.]+), ([\d.]+)\]',line))

if __name__=='__main__':
    g,M,B=normalizers()
    cg=g.exp()
    x1,x2=912559,2278379
    s=sieve(2278383)
    assert sum(s[x1+1:x1+2])==0 and sum(s[x2+1:])==0
    P,a,b=I(1),I(),I()
    for p in range(2,x2+1):
        if not s[p]:continue
        P*=I(p)/(p-1); a+=I(1)/p
        if p<=x1: b+=I(p).ln()/p
    funcs=(
        ('P inverse log .2',D('2278381'),D('2278382'),I('.2'),lambda L:(1-cg*L/P)*L**3),
        ('Q inverse log .2',D('2278381'),D('2278382'),I('.2'),lambda L:(P/(cg*L)-1)*L**3),
        ('reciprocal sum inverse log .2',D('2278382'),D('2278383'),I('.2'),lambda L:(a-L.ln()-M)*L**3),
        ('weighted sum inverse log .3',D('912559'),D('912560'),I('.3'),lambda L:(b-L+B)*L**2),
    )
    for name,l,r,m,f in funcs:
        def z(x):return f(I(x).ln())-m
        assert z(l).l>0>z(r).r
        for _ in range(55):
            w=(l+r)/2
            if z(w).r<0:r=w
            elif z(w).l>0:l=w
            else:
                # Inspect both sides to obtain a bracket even when the
                # midpoint enclosure cannot determine the sign.
                a1=(l+w)/2
                b1=(r+w)/2
                moved=False
                if z(a1).l>0:l=a1;moved=True
                if z(b1).r<0:r=b1;moved=True
                if not moved:break
        print(name,'root bounded by',l,r,'(strict safe real onset at right)')
