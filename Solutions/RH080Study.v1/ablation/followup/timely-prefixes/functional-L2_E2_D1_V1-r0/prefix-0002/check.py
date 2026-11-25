#!/usr/bin/python3.10
"""Directed exact-integer FFT and continuum certificates, no nonstandard modules.

This certifies mathematical inputs, not the C floating search, a Lean proof, or
source-first program verification. For model and error proof see candidate.md.
"""
import argparse, json
from fractions import Fraction as Q
from pathlib import Path
from math import factorial, isqrt

S = 10**35

def need(cond,msg):
    if not cond:
        raise ArithmeticError(msg)

def atan(q):
    a = sum(Q((-1)**i,(2*i+1)*q**(2*i+1)) for i in range(40))
    return a, a + Q(1,81*q**81)

la,ha = atan(5)
lb,hb = atan(239)
PL,PU = 16*la-4*hb,16*ha-4*lb
PC = Q("3.141592653589793238462643383279502884197")
need(PL < PU and PU**2 < 10, "pi")

def roots(L):
    theta=2*PC/L
    need(theta<1 and 2*max(abs(PC-PL),abs(PC-PU))/L < Q(1,S), "angle error")
    # Alternating Taylor at rational center; tails bounded by first omitted term.
    cos0=sum((-1)**j*theta**(2*j)/factorial(2*j) for j in range(14))
    sin0=sum((-1)**j*theta**(2*j+1)/factorial(2*j+1) for j in range(14))
    need(theta**28/factorial(28) < Q(1,S),"Taylor error")
    c, s = int(S*cos0), int(S*sin0)
    W=[(S,0)]
    for k in range(1,L//2):
        a,b=W[-1]
        W.append(((c*a-s*b)//S,(c*b+s*a)//S))
    need(Q(6*L,S)<Q(1,2),"root budget")
    return W

def grid(a,L):
    """Returns integer numerator array plus common complex-grid error fraction."""
    need(L>=64 and L&(L-1)==0 and L>=len(a),"FFT length")
    W=roots(L)
    A=[(0,0)]*L
    for i,v in enumerate(a):
        k=v*S
        need(k.denominator==1,"inexact coefficient on fixed point")
        A[i]=(int(k),0)
    j=0
    for i in range(1,L):
        bit=L//2
        while j&bit:
            j^=bit;bit//=2
        j^=bit
        if j>i: A[i],A[j]=A[j],A[i]
    w=2
    delta=Q(12*L,S)
    while w<=L:
        h=w//2
        step=L//w
        for k in range(0,L,w):
            for b in range(h):
                x,y=A[k+b];u,v=A[k+b+h];c,s=W[b*step]
                u,v=(c*u-s*v)//S,(s*u+c*v)//S
                A[k+b]=(x+u,y+v);A[k+b+h]=(x-u,y-v)
        w*=2
    amp=sum(map(abs,a))
    e=2*L*(delta*amp+Q(2,S))
    need(delta * L < Q(1,2),"FFT error budget")
    return A,e

def posarea(a,b):
    if min(a,b)>=0:return (a+b)/2
    if max(a,b)<=0:return Q(0)
    return max(a,b)**2/(2*abs(a-b))

def primal(m,a,L):
    N=len(a)
    padded=a+[Q(0)]*(L-2*N+1)+a[:0:-1]
    need(len(padded)==L and L>=2*N,"aliased primal")
    V,e=grid(padded,L)
    sample=Q(sum(abs(x) for x,y in V),L*S)
    interpolation=Q(80,12*L**2)*sum(j*j*abs(v) for j,v in enumerate(a))
    J=2*sum(posarea(a[j], b) for j,b in enumerate(a[1:]+[Q(0)]) if j>=m)/m
    f0=(2*sum(a)-a[0])/m
    return sample+e+interpolation,J,f0

def dual(m,a,L,A):
    N=len(a)
    need(L>=2*N and m>=1 and N>m and a[:m]==[Q(1)]*m,"dual shape")
    need(A>=1 and all(1-A<=h<=1 for h in a[m:]),"dual heights")
    jumps=[Q(0)]+[u-v for u,v in zip(a,a[1:]+[Q(0)])]
    V,e=grid(jumps,L)
    sample=max(abs(2*sum(a)/m),
       max((Q(abs(V[k][1]),S)+e)/(PL*Q(m*k,L)) for k in range(1,L//2+1)))
    moment=sum(abs(b)*((j+1)**3-j**3) for j,b in enumerate(a))/(3*m**3)
    return sample + 10*moment*Q(m,L)**2

def read(p):
    d=json.loads(Path(p).read_text())
    m,s=d["m"],d["scale"]
    a=[Q(x,s) for x in d["coefficients"]]
    need(all(type(x)==int for x in d["coefficients"]) and type(m)==int and 1<=m<len(a),
         "rational data")
    return m,a

def up(q,places=15):
    K=10**places
    c=-((-q.numerator*K)//q.denominator)
    sg='-' if c<0 else '';u,v=divmod(abs(c),K)
    return f'{sg}{u}.{v:0{places}d}'

def main():
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['primal','dual'])
    p.add_argument('path')
    p.add_argument('A',type=Q)
    p.add_argument('target',type=Q)
    p.add_argument('--fft',type=int,default=2**17)
    args=p.parse_args();m,a=read(args.path)
    if args.mode=='primal':
        M,J,F0=primal(m,a,args.fft)
        D=F0-args.A*J
        need(D>0,"denominator")
        result=M/D
        print('norm <=',up(M),'leak <=',up(J),'F(0) >=', '-'+up(-F0) if F0<0 else up(F0-Q(1,10**15)))
        if J>0:print('penalty sufficient for target .8, rounded down:', up((F0-Q(5,4)*M)/J-Q(1,10**15)))
    else:
        result=dual(m,a,args.fft,args.A)
        print('coefficient floor (rounded down):',up(1/result-Q(1,10**15)))
    print(args.path,args.fft,'upper bound',up(result))
    need(result<args.target,"target failed")
    print('PASS exact arithmetic')

if __name__=='__main__': main()
