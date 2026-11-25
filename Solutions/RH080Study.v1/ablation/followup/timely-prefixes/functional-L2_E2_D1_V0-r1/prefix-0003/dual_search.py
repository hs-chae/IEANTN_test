
"""Floating-point LP search. Use dual_cert.py separately to certify."""
import math, sys, json
from pathlib import Path
from fractions import Fraction as Q
from operator import itemgetter

def lp(A,b,c):
    # Tableau for Ax<=b, x>=0, maximize c*x. Artificial x for phase one.
    m,n=len(b),len(c)
    D=[list(row)+[-1.,bb] for row,bb in zip(A,b)]
    D.extend([[-cc for cc in c]+[0.,0.],[0.]*n+[1.,0.]])
    N=list(range(n))+[-1]
    B=list(range(n,n+m))
    eps=1.e-10
    def pivot(r,s):
        p=D[r]
        d=1./p[s]
        for i,row in enumerate(D):
            if i==r: continue
            a=row[s]*d
            if abs(a)>1e-15:
                nr=[u-a*v for u,v in zip(row,p)]
                nr[s]=-a
                D[i]=nr
            else: row[s]=0.
        D[r]=[u*d for u in p]
        D[r][s]=d
        N[s],B[r]=B[r],N[s]
    def phase(q):
        r=m+q
        for _ in range(50000):
            s=min((s for s in range(n+1) if q or N[s]!=-1),key=D[r].__getitem__)
            if D[r][s]>=-eps: return
            def skey(i): return D[i][-1]/D[i][s],B[i]
            i=min((i for i in range(m) if D[i][s]>eps),key=skey,default=-1)
            if i<0: raise ArithmeticError('unbounded phase')
            pivot(i,s)
        raise ArithmeticError('iterations')
    r=min(range(m),key=lambda i:D[i][-1])
    if D[r][-1]<-eps:
        pivot(r,n)
        phase(1)
        if abs(D[-1][-1])>eps: raise ArithmeticError('infeasible')
        if -1 in B:
            i=B.index(-1)
            j=max(range(n+1),key=lambda j:abs(D[i][j]))
            pivot(i,j)
    phase(0)
    x=[0.]*n
    for k,i in enumerate(B):
        if i<n: x[i]=D[k][-1]
    return x

def search(A,m,w,path,coarse=0):
    blocks=[(j,j+1) for j in range(m,m*(coarse if coarse else w))]
    if coarse:
        blocks.extend((j,min(j+m//4,m*w)) for j in range(m*coarse,m*w,m//4))
    n=len(blocks)
    off=1-float(A)
    G=240*m
    def basis(k):
        t=k*(m/2)/G
        low=(2*math.sin(2*math.pi*t)/(2*math.pi*t) if t else 2.)
        return [((2*math.sin(math.pi*t*(r-l)/m)/(math.pi*t)) if t else 2*(r-l)/m)
                *math.cos(math.pi*t*(l+r)/m) for l,r in blocks],low
    B=[basis(k) for k in range(G+1)]
    q=set(range(0,G+1,max(1,G//max(140,3*n))))
    for run in range(70):
        mat,bb=[],[]
        for k in sorted(q):
            row,cc=B[k]; bb0=cc+off*sum(row)
            mat.extend([row+[-1.],[-v for v in row]+[-1.]])
            bb.extend([-bb0,bb0])
        for j in range(n):
            r=[0.]*(n+1); r[j]=1.; mat.append(r); bb.append(float(A))
        x=lp(mat,bb,[0.]*n+[-1.])
        v=[min(Q(1),max(1-A,Q(round((a+off)*10**12),10**12))) for a in x[:-1]]
        fv=list(map(float,v))
        U=[abs(cc+sum(k*z for k,z in zip(row,fv))) for row,cc in B]
        print('run',run,'rows',len(q),'sample-min',x[-1],'dense',max(U),flush=True)
        Path(path).write_text(json.dumps(dict(A=str(A),m=m,wing_heights=[str(z) for z,(l,r) in zip(v,blocks) for _ in range(r-l)])))
        if max(U)-x[-1]<1e-8: break
        local=[j for j in range(G+1) if j not in q and (j==0 or U[j]>=U[j-1]) and
               (j==G or U[j]>=U[j+1]) and U[j]>x[-1]+1.e-9]
        if not local: break
        local.sort(key=U.__getitem__,reverse=True)
        q.update(local)
if __name__=='__main__':
    search(Q(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],int(sys.argv[5]) if len(sys.argv)>5 else 0)
