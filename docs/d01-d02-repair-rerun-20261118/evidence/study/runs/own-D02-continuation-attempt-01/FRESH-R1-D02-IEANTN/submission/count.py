from math import isqrt

def primepi(n):
    if n<2:return 0
    q=isqrt(n)
    V=[n//i for i in range(1,q+1)]
    V+=list(range(V[-1]-1,0,-1))
    S={v:v-1 for v in V}
    for p in range(2,q+1):
        if S[p]==S[p-1]:continue
        sp=S[p-1]; pp=p*p
        for v in V:
            if v<pp:break
            S[v]-=S[v//p]-sp
    return S[n]

if __name__=='__main__':
    from decimal import Decimal as D, getcontext
    getcontext().prec=50
    e=D(1).exp()
    p=38358837677; n=p+5
    m=int(D(n)/e)
    a,b=primepi(n),primepi(m)
    print(p,n,m,a,b)
    for i in (D(p),D(n), D(n)+D('.1'), D(n)+D('.9'),D(n+1)):
        print(i,i/e, e*i/i.ln()*b-a*a)
    print('candidate jumps',m*e,(m+1)*e)
