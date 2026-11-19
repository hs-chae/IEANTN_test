from math import isqrt
def primepi(n):
    r=isqrt(n)
    V=[n//i for i in range(1,r+1)]
    V+=list(range(V[-1]-1,0,-1))
    S={v:v-1 for v in V}
    for p in range(2,r+1):
        if S[p]==S[p-1]: continue
        base=S[p-1]
        for v in V:
            if v<p*p: break
            S[v]-=S[v//p]-base
    return S[n]
if __name__=='__main__':
    from intervals import I, exp, log, F
    n=38358837682
    E=exp(1)
    K=14111427770
    assert I(K).lt(n/E) and ((n+1)/E).lt(K+1)
    A,B=primepi(K),primepi(n)
    assert (A,B)==(632207037,1644673232)
    def R(t):return E*t*A/log(t)-B**2
    lo=F(n)+F('.2179263651'); hi=F(n)+F('.2179263652')
    assert R(lo).lt(0) and I(0).lt(R(hi)) and R(n).lt(0)
    print(A,B,str(lo),str(hi),R(lo).pt(),R(hi).pt(),R(n).pt())
