"""Secondary B0; exact principal-value li residual on a short slab."""
import ram_repair as O
from d02_density_new import Q,ep,eu,el
from functools import lru_cache
from math import factorial as fac
from decimal import Decimal

@lru_cache(None)
def res(t):
    assert 25<=t<=45
    N=140
    E,F=ep(t)
    p,q=O.logb(t)
    k=sum(t**j/Q(j*fac(j)) for j in range(1,N+1))
    v=t**(N+1)/Q((N+1)*fac(N+1))/(1-t/(N+2))
    lo=k+p-F*O.H(t)/t
    hi=k+q+1+v-E*O.H(t)/t
    return max(Q(0),lo),hi

def margin(a,b):
    u,v=a-1,b-1
    neg=O.err(u,v)
    L=neg-res(u)[0]*v*el(-v)
    term=b**4*a/(a-1)*L if L>=0 else a**4*b/(b-1)*L
    e=a*eu(-a)*res(b)[1]
    if a>=27 and b<=O.AC:
        e+=-Q('.2089')*el(-b/2)+Q('1.84')*(a/18)*eu(9-a)
        e-=Q('.4178')*el(-b/2)/b*(1-eu((18-a)/2))
    assert O.H(b)+e>0
    sq=a**4*e*(2*O.H(b)+e) if e<0 else b**4*e*(2*O.H(a)+e)
    return O.rem(a,b,4)-term-sq
def run(A,B,z):
    a,b,z=Q(A),Q(B),Q(z)
    pts=sorted({a,b}|{x for x in (O.AC,O.AC+1) if a<x<b})
    stk=list(reversed(list(zip(pts,pts[1:]))))
    mm=Q(100);n=0
    while stk:
        u,t=stk.pop()
        k=margin(u,t)-z
        if k>0:
            mm=min(mm,k);n+=1
        elif t-u<=Q(1,16384):return False,n,k,u,t
        else:
            m=(u+t)/2
            stk.extend([(m,t),(u,m)])
    return True,n,mm,a,b
if __name__=='__main__':
    import sys
    if sys.argv[1:]==['scout']:
        from fractions import Fraction
        p=['27.70','27.74','27.75','27.8','28.23','28.24','28.3','29.18','29.19','29.2','30.58','30.59','30.74','30.75','34.3','43.7']
        for x in p: print(x,float(margin(Q(x),Q(x))),flush=True)
    else:
        for r in [
            ('27.704','27.75','.04'), ('28.17','28.24','.30'),
            ('29.105','29.19','.70'), ('30.577','30.59','1'),
            ('27.8','28.24','.098'), ('28.3','29.19','.367'),
            ('29.2','30.59','.734'), ('30.714','30.75','1.03'),
            ('30.75','43.7','1.037'), ('34.3','43.7','1.406'),
        ]:
            y,n,k,a,b=run(*r)
            print(r,y,n,float(k),float(a),float(b),flush=True)
            assert y

        k,n,a,b=O.adapt('43.7',191,4,'1.037')
        print('early separate old-method join', n,float(k),float(a),float(b),flush=True)
        assert k>0 and b==191
        assert 1+Q(14,388)+Q(145,388**2)>Q('1.037')
        assert 1+Q(14,221)+Q(16,221**2)>Q('1.037')
