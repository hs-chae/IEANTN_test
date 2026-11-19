"""Additional 100-million closed block sweep (B0)."""
from finite_mertens import sieve
from intervals import *
from pathlib import Path
import re
from hashlib import sha256

def normalizers():
    # Transfer the outward enclosures proved and reproduced by finite_mertens.py.
    s=Path(__file__).with_name('finite_run.txt').read_text().splitlines()[1]
    return [I(a,b) for a,b in re.findall(r"\[([.0-9]+), ([.0-9]+)\]",s)]

LIMIT=100000000
START=30000000
STRIDE=128
assert (LIMIT-START)%STRIDE==0
Cs=tuple(map(D,('.081','.08','.075','.07')))
if __name__=='__main__':
    LO.prec=HI.prec=NE.prec=25
    s=sieve(LIMIT)
    print(LIMIT,sum(s),sha256(s).hexdigest(),flush=True)
    gamma,M,B=normalizers()
    cg=gamma.exp()
    prod,a,b=I(1),I(),I()
    def add(i):
        global prod,a,b
        prod*=I(i)/(i-1); a+=I(1)/i; b+=I(i).ln()/i
    for i in range(2,START):
        if s[i]: add(i)
    maxima=[D(0)]*4
    last=[[START]*4 for _ in Cs]
    for x in range(START,LIMIT,STRIDE):
        z=x+STRIDE
        old=(prod,a,b)
        for p in range(x,z+1):
            # For x>START, x was already included.
            if s[p] and (p!=x or x==START): add(p)
        # Weakly include the pre-x state, so this encloses each actual value
        # and both one-sided limits inside the block.
        qp,sp,wp=[I(lo.l,hi.r) for lo,hi in zip(old,(prod,a,b))]
        L=I(I(x).ln().l,I(z).ln().r)
        q=qp/(cg*L)
        vals=[(maxi(f,-f)*L**k).r for f,k in
              ((1/q-1,3),(q-1,3),(sp-L.ln()-M,3),(wp-L+B,2))]
        for j,c in enumerate(Cs):
            for k,v in enumerate(vals):
                if v>=c: last[j][k]=z
        if x>=START:
            maxima=[max(a,b) for a,b in zip(maxima,vals)]
    for c,row in zip(Cs,last):
        assert all(x<LIMIT for x in row)
        print(c,*row)
    print('maxima over blocks starting from 25000000',maxima)
