"""Arbitrary-order factorial lower profiles with explicit terminating onset checks."""
from ramanujan import *
from functools import lru_cache

@lru_cache(None)
def full(j):
    return sum(fac(k)*comb(j,k)-fac(k)*fac(j-k) for k in range(j+1))
@lru_cache(None)
def coeffs(d):
    assert d>=0
    N=d+6
    up=[fac(k) for k in range(N)]+[3*fac(N)]
    co=[sum(fac(k)*comb(j,k) for k in range(min(j,N-1)+1))-
        sum(up[k]*up[j-k] for k in range(N+1) if 0<=j-k<=N)
        for j in range(2*N+1)]
    assert co[:4]==[0]*4 and co[4:N]==[full(j) for j in range(4,N)]
    return N,up,co[N:]
def er(X):
    def up(x):return F(cv(x).hi,S)
    def ep(q):return F(1000,2718)**int(q)
    anc=up(ch100+thetaSpec(I(100)))
    return (F(X,100)*ep(X-100)*anc+
            sum(up(c)*X**k*ep(g*X)*(1+F(X,10000)/(1-g)) for c,g,k in sm))
def succeeds(B,d):
    N,up,co=coeffs(d)
    A=max(32,2*(N+1)); X=B-1
    # e^(A-X) times X^(N+1) < N!/2 ensures both Li barriers.
    if not (X>A and X>8*(9+d)): return False
    if not (2*X**(N+1)*1000**(X-A)<fac(N)*2718**(X-A)):return False
    h=full(N-1)+sum(F(v,B**j) for j,v in enumerate(co,1) if v<0)
    if h<=0:return False
    p=sum(F(v,B**k) for k,v in enumerate(up))
    return h>B**(5+d)*(F(B,B-1)*er(B-1)+er(B)*(2*p+er(B)))
def onset(d):
    a=360
    b=a
    while not succeeds(b,d): b*=2
    # Only a search heuristic; each reported endpoint is verified directly.
    while b-a>1:
        m=(a+b)//2
        if succeeds(m,d):b=m
        else:a=m
    assert succeeds(b,d)
    return b

def new_error(L):
    from density_repair import layers
    e=err(L)
    if L.lo>=140*S and L.hi<=360*S:
        modes=[(I('.011'),F(1,5),2),(I('2.091'),F(1,4),1)]+sm[2:4]
        modes += [(c,g,0) for c,g in layers]
        u=join(L,140,ch140,modes)
        return I.raw(min(e.lo,u.lo),min(e.hi,u.hi))
    return e

if __name__=='__main__':
    assert low(E,F(2718,1000))
    for d in [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,22,24,28,32,40]:
        print('profile degree',d,'certified onset',onset(d))
    import sys
    if 'tight' in sys.argv:
        from density_repair import boot_height
        boot_height()
        for s,c,B,w in [
            ('36.526',(0,),360,True),('36.535',('.005',),360,True),('36.735',('.1',),360,True),
            ('37.766',('.5',),360,True),('39.37',('.9',),360,True),
            ('39.374',('.9',),360,True),
            ('39.98',(1,),360,True),('40.35',('1.05',),290,False),
            ('44.52',('1.2',),80,False),('44.6',('1.2',),81,False),
            ('44.6',('1.2',),80,False),
            ('47.17',('1.3',),56,False),('47.2',('1.3',),56,False),
            ('47.15',(1,14),360,True),('48.2',(1,13,100),360,True),
            ('218',(1,14,145),360,True),('222',(1,14,145),360,True),
            ('254',(1,14,145,1412),360,True),('255',(1,14,145,1412),360,True),('310',(1,14,145,1412,13985),360,True),
            ('351',tuple(full(j) for j in range(4,10)),360,True),
        ]:
            try: run(s,B,c,1000,whole=w,error=new_error)
            except ValueError as e:
                if s not in ('39.37','44.52','47.17','218','254') and (s,B)!=('44.6',81):raise
                print('sufficient-test failure',s,B,c,e)
    for s in ['36.51','36.52','36.53','36.73','37.75','39.35','39.95','40','45','47','47.15','48','58','289','290','320']:
        L=I(s)
        print('diagnostic',s,bound(L))
