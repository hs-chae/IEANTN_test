#!/usr/bin/python3.10
from anchor import *

def ck():
    assert I(24).exp().b<I(10**13).a
    # Verify the unchanged input-independent domain and sign checks in anchor.chk.
    chk()
    cs=list(map(D,['.02209','.02209','.02127']))
    for i,(l,u) in enumerate([(Q(L0.a),Q(24)),(Q(24),K),(K,Q(58)),(Q(58),Q(190)),(Q(190),Q(200))]):
        M=[D(0)]*3
        while l<u:
            r=min(u,l+Q(1,128))
            v=after(l,r)
            if i==0:
                w=anch(l,r)
                v=[mini(t,z) for t,z in zip(v,w)]
            M=[max(x,y.b) for x,y in zip(M,v)]
            l=r
        assert all(x<c for x,c in zip(M,cs))
        print('opt through',u,*[f'{x:.9E}' for x in M])
    assert (I('.01880')*200**2*(-I(25)).exp()).b<min(cs)

if __name__=='__main__':ck()
