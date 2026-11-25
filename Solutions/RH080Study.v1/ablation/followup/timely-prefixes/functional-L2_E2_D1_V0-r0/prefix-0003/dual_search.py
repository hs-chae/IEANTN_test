#!/usr/bin/python3.10
"""Floating LP search only; certify output using window_cert.py."""
import math,sys,json
from fractions import Fraction
from pathlib import Path

def lp(A,b,c):
    # Tableau for max c.x, Ax<=b, x>=0, with shared artificial variable.
    m,n=len(b),len(c)
    D=[a[:]+[-1.,v] for a,v in zip(A,b)]+[[-t for t in c]+[0.,0.],[0.]*n+[1.,0.]]
    B=list(range(n,n+m)); N=list(range(n))+[-1]
    eps=2e-9
    def pivot(r,s):
        row=D[r]; inv=1/row[s]
        for j in range(n+2):
            if j!=s:row[j]*=inv
        row[s]=inv
        for i,rr in enumerate(D):
            if i!=r:
                h=rr[s]
                if h:
                    for j in range(n+2):
                        if j!=s:rr[j]-=h*row[j]
                rr[s]=-h*inv
        B[r],N[s]=N[s],B[r]
    def simplex(phase):
        x=m+1 if phase==1 else m
        for it in range(7000):
            s=min((j for j in range(n+1) if phase==1 or N[j]!=-1),key=lambda j:(D[x][j],N[j]))
            if D[x][s]>=-eps:return True
            inds=[i for i in range(m) if D[i][s]>eps]
            if not inds:return False
            r=min(inds,key=lambda i:(D[i][n+1]/D[i][s], B[i]))
            pivot(r,s)
        raise ArithmeticError('pivot limit')
    r=min(range(m),key=lambda i:D[i][-1])
    if D[r][-1]<-eps:
        pivot(r,n)
        if not simplex(1) or abs(D[m+1][-1])>eps:raise ValueError('infeasible')
        if -1 in B:
            r=B.index(-1); s=max(range(n+1),key=lambda j:abs(D[r][j]))
            if abs(D[r][s])>eps:pivot(r,s)
    if not simplex(2):raise ValueError('unbounded')
    result=[0.]*n
    for i,k in enumerate(B):
        if k<n:result[k]=D[i][-1]
    return result

A=Fraction(sys.argv[1]); m=int(sys.argv[2]); N=m*int(sys.argv[3]); target=sys.argv[4]; G=int(sys.argv[5]) if len(sys.argv)>5 else 4096
def bval(j,k):
    if k==0:return 2/m
    s=math.pi*k/G
    return (math.sin(s*(j+1))-math.sin(s*j))/(s*m/2)
base=1-float(A); n=N-m
matrix=[]
for k in range(G+1):
    u=[bval(j,k) for j in range(m,N)]
    intercept=sum(bval(j,k) for j in range(m))+base*sum(u)
    matrix.append((u,intercept))

selected=set(range(0,G+1,max(1,G//(2*n))))
best=1e100
for i in range(35):
    AA=[[float(j==k) for j in range(n)]+[0.] for k in range(n)]
    rhs=[float(A)]*n
    for k in sorted(selected):
        u,v=matrix[k]
        AA.extend([u+[-1.],[-z for z in u]+[-1.]])
        rhs.extend([-v,v])
    *sol,M=lp(AA,rhs,[0.]*n+[-1.])
    errs=[abs(sum(a*b for a,b in zip(sol,u))+v) for u,v in matrix]
    err=max(errs)
    print(i,len(selected),M,err,flush=True)
    if err<best:
        best=err
        w=[min(Fraction(1),max(1-A,Fraction(round(10**11*(s+base)),10**11))) for s in sol]
        Path(target).write_text(json.dumps({'A':str(A),'m':m,'wing_heights':list(map(str,w))},indent=2)+'\n')
    if err<=M+1e-8:break
    # Insert the most-violated samples, spread across the interval.
    blocks=[0,G+1]
    added=[]
    for k in sorted(range(G+1),key=lambda k:errs[k],reverse=True):
        if errs[k]<M+max(1e-8,(err-M)*.04):break
        if k not in selected and all(abs(k-j)>=max(1,G//(5*n)) for j in added):
            added.append(k);selected.add(k)
        if len(added)>=max(5,n//2):break
    if not added:break
