"""Counterexamples to certificate targets, not to arithmetic inequalities."""
from d02m import *
import d02ram as r
from d02screen import classic

if __name__=='__main__':
    A_H=PI/(H-1)+(PI/H)**2/3
    v=log(H/(2*PI)); d_H=(v*v-v/3)/(2*PI)
    assert A_H<A0 and d_H<I('113.67')
    assert A_H*184**2>I('3.54e-8') and A_H*e(I(184)/8)>I('.01')
    assert I('.245')*e(-a*I(175))<A_H
    print('Original-input boundary constants A_H, d_H:',A_H,d_H,flush=True)
    L=F('167.84'); x=I(L)
    p=r.polyr(L,6,17)-r.loss(L,L,6,17,shift=F('1.001'))-r.qerr(L,L,6,17)-r.shiftcost(L,68)
    assert p<I(1)
    print('Zero-width reserve at L=167.84 for the 68-shift test:',p,flush=True)
    v=bz(L)/(1-bz(L)/x)
    w=combined(L)*e(-a*x)
    for q,al,target in [(0,F(1,8),'.001350'),(0,F(9,64),'.018165'),
                        (0,a,'.249412'),(2,F(0),'2.944e-8')]:
        f=x**q*e(al*x)
        assert v*f>I(target) and w*f>I(target)
        print('Point L=167.84: both computed upper functions exceed target',q,al,target,v*f,w*f,flush=True)
    for c in (F('.24'),F('.25'),F('.27'),F('.28')):
        print('Exploratory cutoff at 155, not used for domain claims',c,sharp(F(155),c),flush=True)
    Z=F(200)
    assert combined(Z)>I('.212654')
    print('The repaired common curve still exceeds the old target at 200:',combined(Z),flush=True)
