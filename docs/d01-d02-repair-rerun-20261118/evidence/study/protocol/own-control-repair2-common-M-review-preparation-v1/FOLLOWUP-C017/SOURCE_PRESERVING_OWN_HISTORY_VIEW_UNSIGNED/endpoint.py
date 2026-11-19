from intervals import *
from math import isqrt
def primepi(n):
    # Each distinct floor(n/k) or small integer is a key.
    rt=isqrt(n)
    vals=[n//k for k in range(1,n//(rt+1)+1)]+list(range(rt,0,-1))
    C={v:v-1 for v in vals}
    for p in range(2,rt+1):
        if C[p]==C[p-1]: continue
        a=C[p-1]
        for v in vals:
            if v<p*p: break
            C[v]-=C[v//p]-a
    return C[n]

if __name__=='__main__':
    n=38358837682
    ly=n/E; ry=(n+1)/E
    print('x/e on [n,n+1]:',ly,ry)
    f=int(ly.l)
    print('neighbor floors:',f,int(ry.r))
    ps=primepi(n)
    qs=primepi(f)
    assert primepi(n+1)==ps
    assert primepi(int(ry.r))==qs
    print('pi(x), pi(x/e):',ps,qs)
    def R(a):
        a=I(a)
        return E*a/a.ln()*qs-ps*ps
    for a in (str(n),'38358837682.01','38358837682.1','38358837682.5',str(n+1)):
        print('R(',a,')=',R(a))
    a,b=D(n),D(n+1)
    for i in range(32):
        m=(a+b)/2
        Rm=R(m)
        assert Rm.r<0 or Rm.l>0
        if Rm.r<0:a=m
        else:b=m
    print('last zero in ',a,b)
    assert R(a).r<0<R(b).l
