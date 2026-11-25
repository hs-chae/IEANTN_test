
"""Candidate generation (not relied on in affine window certificate)."""
from decimal import Decimal as D,localcontext
from pathlib import Path
import json,sys
from gauss_cert import fourier,Q

def main(file,m,R,out):
    p=[Q(z) for x in json.loads(Path(file).read_text()) for z in (x,0)][:-1]
    g=fourier(p)
    with localcontext() as ctx:
        ctx.prec=80
        pi=D('3.14159265358979323846264338327950288419716939937510')
        c=[D(x.numerator)/D(x.denominator) for x in g[::2]]
        s=10**16
        a=[]
        for j in range(m*R):
            v=pi*(D(j)/m)**2
            w=D(0)
            for x in reversed(c): w=w*v+x
            a.append(round(w*(-v).exp()*s))
    Path(out).write_text(json.dumps(dict(m=m,scale=s,coefficients=a)))
if __name__=='__main__':
    main(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4])
