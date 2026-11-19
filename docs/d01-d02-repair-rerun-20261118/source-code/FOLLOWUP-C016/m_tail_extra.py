#!/usr/bin/python3.10
from mertens import *
def ck():
    for m in (0,1):
        a,*_=spectralparts(m)
        for L,c in [(155,'.22320' if not m else '.51687'),
                    (169,'.26100' if not m else '.32619'),
                    (200,'.018791' if not m else '.25973')]:
            if m==0 and L==169: continue
            z=pure(Q(L),m)
            assert all(x.b<D(c) for x in z)
            print('clean',m,L,c)
        for kind,limit,lo_,hi_ in [('first','1e-14',150,186 if m==0 else 167),
                                    ('weighted','1e-12',150,190 if m==0 else 170)]:
            def bound(L):
                v=I(L)
                return pure(L,m)[0 if kind=='first' else 2]*(-I(a)*v).exp()/(v if kind=='first' else 1)
            l,r=lo_*16,hi_*16
            assert bound(Q(r,16)).b<D(limit)
            while l<r:
                x=(l+r)//2
                if bound(Q(x,16)).b<D(limit):r=x
                else:l=x+1
            L=Q(l,16)
            H=bound(L)
            assert H.b<D(limit)
            print('fixed',m,kind,limit,L,f'{H.b:.9E}')
    # Matched clean coefficients: strict dominance on overlap L>=200.
    assert (I('.25973')/I('.018791')*(-I(Q(200,32))).exp()).b<1
    assert (I('.25973')*(-I(Q(200,32))).exp()).b<D('.01')

if __name__=='__main__':ck()
