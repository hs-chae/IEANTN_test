#!/usr/bin/python3.10
"""Ancillary endpoint, constant, and readback checks; not an independent new method."""
import sys
sys.path.insert(0,'/work/exact-review')
from cert import *
from mertens import pure,spectralparts
from endpoint import pi,gap,N
assert gap(N+Q('0.001')).b<0
print('literal PT PNT real counterexample',gap(N+Q('0.001')))
for m,first,weighted in [(0,'1.305e-15','2.610e-13'),(1,'3.482e-17','6.964e-15')]:
    a,*_=spectralparts(m)
    p=pure(Q(200),m)
    obs=[z*(-I(a)*200).exp()/(200 if i<2 else 1) for i,z in enumerate(p)]
    assert max(z.b for z in obs[:2])<D(first)
    assert obs[-1].b<D(weighted)
    print('M6 at 200',m,*obs)
assert (I('.01880')*200**2*(-I(25)).exp()).b<D('.02127')
assert (I('.3')*(-I(Q(5,32)*200)).exp()*(1+1/(I(200)*(Q(1,2)-Q(2,58))))).b<CH[0][0].a
x=I(10**8)
cap=I('1.791000147')/x**Q(1,2)+I('1.78')/x**Q(2,3)
assert D('.000181')<cap.a<=cap.b<D('.000188')
print('cap at 1e8: failed old sufficient budget .000181, passed .000188',cap)
assert I('21.41').exp().b<D(2*10**9)
assert 1<I('21.41').a
