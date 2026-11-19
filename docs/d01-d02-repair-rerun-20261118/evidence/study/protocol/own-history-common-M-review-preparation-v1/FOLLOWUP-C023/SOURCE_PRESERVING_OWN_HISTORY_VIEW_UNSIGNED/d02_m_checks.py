from d02_m_new import *
from d02_density_new import spectral
LOG_JOINS=[
 (D0,'59.99','4.27e-8','189.13'),
 (D0,'60.15','4e-8','189.13'),
 (D,'60.855','2.9873e-8','168.901'),
 (D0,'60.34','3.75e-8','189.13'),
]
LOG_POWER=[
 ('171','2.16e-8'), ('172','1.86e-8'), ('176.18','1e-8'),
 ('180','5.59e-9'), ('184.2','3e-9'), ('191.5','1e-9'), ('200','2.79e-10'),
]
POWER=[
 (169,'.300102'), (170,'.298321'), (190,'.269799'), (200,'.259244'),
 (250,'.225620'), (400,'.188868'), (600,'.173283'), (1000,'.162328'),
 (2500,'.152450'), (10000,'.147651'), (100000,'.146183'),
 (1000000,'.146038'), (5000000,'.146025'),
]
def logpower(a,k):
    A,K=Q(a),Q(k)
    assert A>2/D
    v=logscale(A,D,'power')
    print('pure power used as log ray',A,K,float(v),flush=True)
    assert v<=K
def trade(a,d,p,K):
    A,d,K=Q(a),Q(d),Q(K)
    assert 0<=d<D and p>=0 and A*(D-d)>=p
    v=U(A)*eu(-(D-d)*A)*A**p
    print('log-power trade',A,d,p,K,float(v),flush=True)
    assert v<=K
def compare():
    A=Q(169)
    # Same method: certify an actual failed scale comparison of its B0
    # radius (not merely failure of a sufficient upper-enclosure test).
    B=Q(188)
    assert spectral(B,D0,1,el)*el(-D0*B)>q
    assert B*B*q>Q('2.9873e-8')
    # Entire D02 ray versus all displayed frozen B0 power coefficients.
    assert U(A)*eu(-(D-D0)*A)<Q('.01044')
    print('B0 envelope at 188 exceeds',float(B*B*q),'; D02 coefficient in B0 power units at 169 is at most',
          float(U(A)*eu(-(D-D0)*A)),flush=True)
    assert F(Q(200))<Q('.260')
if __name__=='__main__':
    from sys import argv
    if argv[1:]==['scout']:
        for b in ('86.5','86.75','87','87.1','87.2','87.5','88'):
            print('positive',b,float(under(b)),flush=True)
        for a in (170,180,190,200,210,220,230,250,400,1000):
            print('prim',a,*(float(x) for x in prim(a)),flush=True)
        power(5000000,1,D0,verify=False)
        for args in [(200,Q(9,64),1,10),(400,D0,2,10),(500,D0,3,10),(600,D0,3,10)]:
            trade(*args)
    else:
        compare()
        for d,a,k,b in LOG_JOINS:logray(a,k,b,d)
        for a,k in LOG_POWER:logpower(a,k)
        for a,k in POWER:power(a,k)
        power(5000000,'.010443',D0)

        for d,b,k in [(D0,'85.7','.10'),(D,'86.5','.35'),(D,'86.75','.23'),(D,'86.99','.10'),(D,'87.15','0')]:
            a=under(b,d)
            print('primorial positivity slab [84.5,B]',d,b,k,float(a),flush=True)
            assert a>Q(k)
        for a,lo,hi in [(170,'6.063e-14','1.91e-13'),(180,'5.785e-14','8.234e-14'),
                        (190,'5.554e-14','6.022e-14'),(200,'5.361e-14','5.451e-14'),
                        (210,'5.196e-14','5.213e-14'),(230,'4.931e-14','4.931e-14'),
                        (400,'4.005e-14','4.005e-14'),(1000,'3.470e-14','3.470e-14')]:
            u,v=prim(a)
            print('primorial power ray',a,float(u),float(v),flush=True)
            assert u<Q(lo) and v<Q(hi)
        for args in [(200,Q(9,64),1,'2.279'),(400,D0,2,'.11262'),
                     (500,D0,3,'3.668'),(600,D0,3,'.26928')]:
            trade(*args)
