import math, json, sys
from pathlib import Path
from math import sqrt,exp
# Orthonormal-scaled Laguerre (alpha=-1/2) times e^(-u^2); Fourier eigenvalue (-1)^n.
def basis(u,N):
    q=u*u
    p=[exp(-q)]
    if N:
        p.append((.5-2*q)*p[0]/sqrt(.5))
    for n in range(1,N):
        p.append(((2*n+.5-2*q)*p[n]-sqrt(n*(n-.5))*p[n-1])/sqrt((n+1)*(n+.5)))
    return p

def solve(a,b):
    a=[r[:] + [x] for r,x in zip(a,b)]
    n=len(b)
    for i in range(n):
        j=max(range(i,n),key=lambda q:abs(a[q][i]))
        a[i],a[j]=a[j],a[i]
        d=a[i][i]
        for j in range(i+1,n):
            t=a[j][i]/d
            for k in range(i+1,n+1):
                a[j][k]-=t*a[i][k]
    x=[0.]*n
    for i in reversed(range(n)):
        x[i]=(a[i][-1]-sum(a[i][j]*x[j] for j in range(i+1,n)))/a[i][i]
    return x

def main(N,A,step,init=None):
    p0=basis(0,N)[1:]
    # Midpoint mesh, split precisely at sqrt(pi).
    B=[]
    for a,b,k in [(0,sqrt(math.pi),0),(sqrt(math.pi),sqrt(2*N)+5,1)]:
        n=math.ceil((b-a)/step)
        h=(b-a)/n
        for i in range(n):
            v=basis(a+(i+.5)*h,N)
            B.append((v[0],tuple(x-v[0]*y for x,y in zip(v[1:],p0)),h,0))
            if k:
                B.append((v[0],tuple(((-1)**j)*x-v[0]*y for j,(x,y) in enumerate(zip(v[1:],p0),1)),h,1))
    dot=lambda b,x:sum(p*q for p,q in zip(b,x))
    def calc(x,mu,c,want):
        f=0.
        if want:
            g=[0.]*N; H=[[0.]*N for _ in range(N)]
        for a,b,h,k in B:
            z=a+dot(b,x)
            if k: h*=c*A/2
            s=sqrt(z*z+mu*mu)
            f+=h*(s+k*z)
            if want:
                r=h*(z/s+k)
                for i in range(N):g[i]+=r*b[i]
                w=h*mu*mu/(s*s*s)
                if w>1e-12:
                    for i in range(N):
                        v=w*b[i]
                        for j in range(i+1):H[i][j]+=v*b[j]
        if want:
            for i in range(N):
                H[i][i]+=1e-12
                for j in range(i):H[j][i]=H[i][j]
            return f,g,H
        return f
    x=[0.]*N if init is None else init[:N]+[0.]*max(0,N-len(init))
    c=.84 if A>3 else .8
    for mu in (.01,.002,.0004,.00008,.000016,.0000032,.00000064,.000000128):
        for i in range(35):
            f,g,H=calc(x,mu,c,True)
            d=solve(H,[-v for v in g]); slope=dot(g,d)
            if -slope<1e-14:break
            t=1.
            while True:
                y=[p+t*q for p,q in zip(x,d)]
                v=calc(y,mu,c,False)
                if v<=f+t*.01*slope or t<1e-10:break
                t*=.5
            x=y
        M=L=0.
        for a,b,h,k in B:
            z=a+dot(b,x)
            if k:L+=h*max(0,z)
            else:M+=h*abs(z)
        M*=2/sqrt(math.pi); L*=2/sqrt(math.pi)
        c=M/(1-A*L) if A>3 else .8
        print(N,A,mu,i,M,L,M/(1-A*L),(1-1.25*M)/L,flush=True)
        dest=Path('/work',f'g{N}_{A}.json')
        dest.write_text(json.dumps({'N':N,'A':A,'x':x,'M':M,'L':L,'mu':mu}))
    return x
if __name__=='__main__':
    N,A,step=int(sys.argv[1]),float(sys.argv[2]),float(sys.argv[3])
    init=json.loads(Path(sys.argv[4]).read_text())['x'] if len(sys.argv)>4 else None
    main(N,A,step,init)
