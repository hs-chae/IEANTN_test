"""Matched-coefficient and simple power crossover comparisons."""
from mertens_d02 import *
from gap_d02 import Model
def checks():
    # r(t)=.25665/.01322 * exp(-t/32) strictly decreases.
    t=32*log(I('.25665')/I('.01322'))
    less(94,t); less(t,95)
    print('simple power crossover',approx(t),flush=True)
    # Direct assumption is not the chosen magnitude on its whole legal ray.
    less(2800*cs(I(200),J),625)
    print('D02 strip-transfer point radius < raw D02 radius / 2800, t >= 200',flush=True)
    # Diagnostic obstruction for the common reconstructed proof, not for R.
    M=Model(14,24)
    q=M.gap(I(185),Q,6)
    j=M.gap(I(185),J,6)
    less(q,27); less(144,j)
    print('two baseline/narrow-strip lower expressions, degree 6 at t=185',approx(q),approx(j),flush=True)
    for c in ['.012400','.01322']:
        less(I('.21771')*exp(I(-200)/32),c)
    for tau,c,base in [(98,'.25665','.012400'),(117,'.25665','.006665'),
                       (200,'.21771','.000421')]:
        less(I(c)*exp(I(-tau)/32),base)
        print('same b=7/8 power-shaped cap',tau,base,flush=True)
    print('power rows strictly improve over indicated old exponent rows at 200 and thereafter',flush=True)
if __name__=='__main__': checks()

