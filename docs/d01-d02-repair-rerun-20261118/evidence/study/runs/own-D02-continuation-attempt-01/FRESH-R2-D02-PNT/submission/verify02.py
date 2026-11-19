"""Exact finite obligations and analytic-tail guards for the new claims."""
import sys
if sys.flags.optimize: raise RuntimeError('run with assertions enabled')
from early02 import *
from compare02 import run_compare

M2=[(170,'.258'),('175.1','.25'),(180,'.243'),(190,'.231'),(200,'.221'),(210,'.213'),
    (225,'.202'),(250,'.189'),(300,'.173'),(350,'.162'),(420,'.153'),(600,'.141'),
    (1000,'.130'),(2000,'.122'),(10000,'.1166'),(100000,'.11563'),(1000000,'.115568')]
M0=[(180,'.0141'),(200,'.01277'),(225,'.01167'),(250,'.01092'),(300,'.00995'),
    (350,'.00935'),(420,'.00882'),(600,'.00810'),(1000,'.00750'),(2000,'.00705'),
    (10000,'.00673'),(100000,'.006671'),(1000000,'.006668')]
RI2=[(173,'.815'),(181,'.776'),(191,'.737'),(200,'.71'),(211,'.677'),(251,'.602'),
     (301,'.549'),(421,'.485'),(601,'.446'),(1001,'.412'),(2001,'.388'),
     (10001,'.370'),(1000001,'.367')]
RI0=[(201,'.041')]
AR=[(5,266,324),(6,292,359),(7,318,394),(8,345,429),(9,372,465),(10,398,501),
    (11,425,537),(12,452,573),(13,479,610),(14,506,646),(15,534,682),
    (16,561,719),(17,588,755),(18,615,791),(20,670,864),(22,725,938),
    (24,780,1011),(28,889,1157),(32,999,1304),(40,1219,1597),
    (50,1494,1964),(60,1770,2334),(80,2321,3070)]
def P(d):
    return tuple(ro.full(j) for j in range(4,5+d))

def merits():
    for z,rr in [(0,M2),(1,M0)]:
        for B,C in rr:m_tail(B,C,z)
    for z,C,B in [(0,'.262',173),(1,'.015',193)]:
        finite_m(C,13,B,z)
        m_tail(B,C,z)
    m_tail('181.1','.014',1)

def ram():
    assert low(E,F(2718,1000))
    r.boot(); early_boot(); r.endpoint()
    for l,c in [('27.9',(0,)),('28.35',('.1',)),('29.5',('.5',))]:ec(l,'30.9',c,False)
    for l,c in [
       ('27.8',(0,)),('27.95',('.1',)),('28.75',('.5',)),('29.95',('.9',)),
       ('30.4',(1,)),('31',('1.05',)),('31.85',('1.2',)),('32.75',('1.3',)),
       ('33',(1,9)),('34.2',('1.4',)),('38',(1,14)),('39',(1,13,100))]:
        ec(l,'43.74',c)
    for c in [('1.2',),(1,9)]:r.run('43.74',80,c,1000,whole=False,error=pi_book)
    for l,t,c in [
       ('36.525',70,(0,)),('36.534',37,('.005',)),
       ('36.732',37,('.1',)),('37.762',38,('.5',)),('39.37',70,('.9',)),('39.972',41,(1,)),
       ('40.34',290,('1.05',)),('44.59',80,('1.2',)),
       ('47.13',100,(1,14)),('48.15',101,(1,13,100)),('60',90,P(3))]:
        r.run(l,t,c,1000,whole=False,error=lambda u:pi_bound(u,1))
    if 'local' in sys.argv:local()
    for l,t,d in [('185.5',196,2),('210',217,3),('235.5',241,4)]:
        r.run(l,t,P(d),1000,whole=False,error=lambda u:pi_bound(u,0))
        assert tail_R(t,d)
        print('D02 connected higher profile',l,t,d,flush=True)
    r.run('172',196,(1,14,100),1000,whole=False,error=lambda u:pi_bound(u,0))
    for l,t,d in [('218',227,2),('250',257,3),('284',290,4)]:
        r.run(l,t,P(d),1000,whole=False,error=lambda u:pi_bound(u,1))
        assert tail_R(t,d,1)
        print('B0 connected higher profile',l,t,d,flush=True)
    for z,rr in [(0,RI2),(1,RI0)]:
        for B,C in rr:li_residual(B,C,z)
    for d,b,c in AR:
        assert tail_R(b,d),(d,b)
        assert tail_R(c,d,1),(d,c)
        print('confirmed matched tail',d,b,c,flush=True)

if __name__=='__main__':
    basics(); boot_height(); run_compare()
    if 'R' in sys.argv or 'M' not in sys.argv:ram()
    if 'M' in sys.argv or 'R' not in sys.argv:merits()
    print('VERIFIED new obligations',sys.argv[1:],flush=True)
