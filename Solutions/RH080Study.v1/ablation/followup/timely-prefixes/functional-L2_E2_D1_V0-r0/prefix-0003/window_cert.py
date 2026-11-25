#!/usr/bin/python3.10
"""Exact fixed-point FFT; step dual and polygonal primal certificates."""
import argparse,json
from math import factorial,lcm
from fractions import Fraction as Q
from pathlib import Path
from gauss_cert import pi_bounds,decimals
S=10**28
# Short rational pi bounds from the Machin bounds.
pl,pu=pi_bounds()
p=(pl*10**46).__floor__()
assert pu < Q(p+1,10**46)
PI=Q(p,10**46)
assert 3 < PI and Q(p+1,10**46)**2 < 10

def fft(values,L):
    assert L>=256 and L&(L-1)==0 and len(values)<=L
    t=2*PI/L
    assert 2*Q(1,10**46)/L+t**24/factorial(24)<Q(1,S)
    c=(S*sum(((-1)**j*t**(2*j)/factorial(2*j) for j in range(12)),Q(0))).__floor__()
    s=(S*sum(((-1)**j*t**(2*j+1)/factorial(2*j+1) for j in range(12)),Q(0))).__floor__()
    tw=Q(12*L,S)
    assert Q(4*L,S)<Q(1,2) and (L.bit_length()-1)*tw/2<Q(1,2)
    re=[S];im=[0]
    for k in range(1,L//2):
        a,b=re[-1],im[-1]
        re.append((a*c-b*s)//S)
        im.append((a*s+b*c)//S)
    R=values+[0]*(L-len(values));I=[0]*L
    j=0
    for i in range(1,L):
        h=L//2
        while j&h:
            j^=h
            h//=2
        j^=h
        if i<j:R[i],R[j]=R[j],R[i]
    w=2
    while w<=L:
        half=w//2;step=L//w
        for i in range(0,L,w):
            for k in range(half):
                j=i+k
                v=j+half
                a,b=R[v],I[v]
                c,s=re[k*step],im[k*step]
                x,y=(a*c-b*s)//S,(a*s+b*c)//S
                p,q=R[j],I[j]
                R[j],R[v]=p+x,p-x
                I[j],I[v]=q+y,q-y
        w*=2
    # Exact input is values in integer units. Output R,I and abs error in same units.
    e=2*L*(tw*sum(map(abs,values))+2)
    return R,I,e

def dual(path,L,A=None,target=None):
    d=json.loads(Path(path).read_text())
    m=d['m']
    if A is None:A=Q(d['A'])
    b=[Q(1)]*m+list(map(Q,d['wing_heights']))
    assert A>=1 and all(1-A<=h<=1 for h in b)
    C=lcm(*(h.denominator for h in b))
    M=C*10**13
    jumps=[a-z for a,z in zip(b,b[1:]+[0])]
    inp=[0]+[int(x*M) for x in jumps]
    assert len(inp)<=L//2
    _,FX,err=fft(inp,L)
    nom,k=max(((Q(abs(FX[k])+err,k),k) for k in range(1,L//2+1)))
    exact0=abs(2*sum(b)/m)
    grid=max(exact0,nom*L/(PI*m*M))
    # ||Vcheck''||_infty <= 8 pi^2 sum |b_j| ((j+1)^3-j^3)/(3m^3).
    interp=Q(10,3*m*L**2)*sum(abs(a)*(3*j*j+3*j+1) for j,a in enumerate(b))
    tot=grid+interp
    print(path,'L=',L,'A=',A,'sample argmax index',k,'scaled 1e12:',decimals(grid,12)[1],decimals(interp,12)[1],decimals(tot,12)[1],flush=True)
    if target:
        assert tot<target
        print('PROVED Cplus <= bound <',target,flush=True)
    return tot

def positive_area(a,b):
    if a>=0 and b>=0:return (a+b)/2
    if a<=0 and b<=0:return Q(0)
    return max(a,b)**2/(2*abs(a-b))

def primal(path,L,A=None,target=None):
    d=json.loads(Path(path).read_text())
    m=d['m']; scale=d['scale']; a=d['coefficients']; n=len(a)
    if A is None:A=Q(d['A'])
    assert L>=2*n and A>=0
    inp=[x*10**13 for x in a]+[0]*(L-2*n+1)+[x*10**13 for x in reversed(a[1:])]
    assert len(inp)==L
    real,_,e=fft(inp,L)
    U=(Q(sum(map(abs,real)),L)+e)/(scale*10**13)
    U+=Q(80,12*L**2*scale)*sum(j*j*abs(c) for j,c in enumerate(a))
    b=[Q(c,scale) for c in a]+[Q(0)]
    J=2*sum(positive_area(v,w) for v,w in zip(b[m:],b[m+1:]))/m
    v=(2*sum(b)-b[0])/m
    D=v-A*J
    assert D>0
    r=U/D
    print(path,'L=',L,'A=',A,'mass, leak, ratio scaled 1e12:',*(decimals(q,12)[1] for q in (U,J,r)),flush=True)
    if target:
        assert r<target
        print('PROVED R <',target,flush=True)
    return U,J,v

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['dual','primal']);p.add_argument('file');p.add_argument('power',type=int)
    p.add_argument('--A',type=Q);p.add_argument('--target',type=Q)
    a=p.parse_args()
    (dual if a.mode=='dual' else primal)(a.file,2**a.power,a.A,a.target)
