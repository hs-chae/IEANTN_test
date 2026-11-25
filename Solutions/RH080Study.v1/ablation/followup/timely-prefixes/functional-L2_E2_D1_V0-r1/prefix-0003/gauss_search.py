
"""Floating search only. Optimization coordinate h_j=(H_{2j}(sqrt(2)y) exp(-y^2))/sqrt(2^{2j}(2j)!).
Fourier eigenvalue (-1)^j; x=y/sqrt(pi). Outputs rational monomial coefficients in y."""
import math,sys,json
from decimal import Decimal, localcontext
from pathlib import Path

def hermites(y,n):
    z=math.exp(-y*y)
    w=2*y*z
    a=[z]
    for j in range(2,2*n+1):
        z,w=w,(2*y*w-math.sqrt(j-1)*z)/math.sqrt(j)
        if j%2==0: a.append(w)
    return a

def solve(M,g):
    n=len(g)
    M=[r[:] + [g[k]] for k,r in enumerate(M)]
    for i in range(n):
        k=max(range(i,n),key=lambda k:abs(M[k][i]))
        M[k],M[i]=M[i],M[k]
        r=M[i]
        d=r[i]
        for k in range(i+1,n):
            s=M[k]; q=s[i]/d
            for j in range(i+1,n+1): s[j]-=q*r[j]
    x=[0.]*n
    for i in reversed(range(n)): x[i]=(M[i][-1]-sum(M[i][j]*x[j] for j in range(i+1,n)))/M[i][i]
    return x

def make(n,A,r,step,s=1.):
    sq=math.sqrt(math.pi)
    v=hermites(0,n)
    out=[]
    for iswing,st,en,w in [(False,0,max(10,math.sqrt(4*n)+3),1/s),(True,sq/s,max(10,math.sqrt(4*n)+3),r*A/2)]:
        nb=math.ceil((en-st)/step)
        dx=(en-st)/nb
        for i in range(nb):
            u=st+dx*(i+.5); a=hermites(u,n)
            if iswing: a=[z*(-1)**j for j,z in enumerate(a)]
            # second term of (sqrt(z^2+eps^2)+z)/2 included in sign.
            out.append((a[0], [a[j]-a[0]*v[j] for j in range(1,n+1)], 2*dx/sq*w, iswing))
    return out

def evaluate(rows,c,eps,hess):
    n=len(c)
    f=0.; g=[0.]*n; H=[[0.]*n for j in range(n)]
    for b,a,w,wing in rows:
        z=b+sum(aj*cj for aj,cj in zip(a,c))
        q=math.sqrt(z*z+eps*eps)
        f+=w*(q+z*wing)
        if hess:
            s=w*(z/q+wing)
            t=w*eps*eps/q**3
            if t < 1e-11 and abs(s)<1e-13: continue
            for j,aj in enumerate(a):
                g[j]+=s*aj
                taj=t*aj
                for k in range(j+1): H[j][k]+=taj*a[k]
    if not hess: return f
    for j in range(n):
        H[j][j]+=1e-10
        for k in range(j): H[k][j]=H[j][k]
    return f,g,H

def output(c,path):
    with localcontext() as ctx:
        ctx.prec=80
        p,q=[1],[0,4] # H recurrence wrt y with rescaling: normalized h_n = R_n/(2^n sqrt(n!))
        # R_n=(sqrt(2))^n H_n(sqrt(2)y): R_1=4y; R_n=4y R_{n-1}-4(n-1)R_{n-2}.
        v=hermites(0,len(c))
        c=[1-sum(v[j+1]*x for j,x in enumerate(c))]+list(c)
        m=[Decimal(c[0])]+[Decimal(0)]*(len(c)-1)
        for j in range(2,2*len(c)-1):
            p,q=q,[4*(q[k-1] if k else 0)-4*(j-1)*(p[k] if k<len(p) else 0) for k in range(j+1)]
            if j%2==0:
                t=Decimal(c[j//2])/(2**j*Decimal(math.factorial(j)).sqrt())
                for k in range(0,j+1,2): m[k//2]+=t*q[k]
        m[0]=Decimal(1)
        Path(path).write_text(json.dumps([str(x.quantize(Decimal('1e-55'))) for x in m]))
if __name__=='__main__':
    A,r=float(sys.argv[1]),float(sys.argv[2])
    n=int(sys.argv[3]); fn=sys.argv[4]
    c=[0.]*n
    scale=float(sys.argv[6]) if len(sys.argv)>6 else 1.
    if len(sys.argv)>5:
        cc=json.loads(Path(sys.argv[5]+'.c').read_text())
        c[:min(n,len(cc))]=cc[:n]
    for eps,step,it in [(1e-3,.02,10),(1e-4,.01,9),(1e-5,.005,12),(1e-6,.002,15),(1e-7,.001,14),(1e-8,.0005,18),(1e-9,.00025,16)]:
        rows=make(n,A,r,step,scale)
        for i in range(it):
            f,g,H=evaluate(rows,c,eps,True)
            d=solve(H,g)
            alpha=1.
            while alpha>1e-7:
                cc=[x-alpha*y for x,y in zip(c,d)]
                if evaluate(rows,cc,eps,False)<f: c=cc; break
                alpha*=.5
            if alpha*max(map(abs,d))<1e-9: break
        print(eps, f, 'F-r',f-r,flush=True)
        output(c,fn)
        Path(fn+'.c').write_text(json.dumps(c))
