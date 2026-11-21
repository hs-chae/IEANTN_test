#!/usr/bin/python3.10
"""Exact rational scalar certificate, NOT source-first PV. See Ramanujan.md."""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial as fac
import re
from pathlib import Path
D = 10**44
def req(h, *e):
    if not h: raise ValueError(e)
def down(q): return Q(q.numerator * D // q.denominator,D)
def up(q): return -down(-q)

@lru_cache(None)
def expi(x):
    if x < 0:
        a,b=expi(-x)
        return down(1/b),up(1/a)
    req(x<=44,'exp range',x)
    t=Q(1); s=t
    for k in range(1,156):
        t*=x/k;s+=t
    return down(s),up(s+t*x/(156-x))

def logi(x):
    req(x>=1)
    k=0
    while x>2: x/=2;k+=1
    def l(y):
        u=(y-1)/(y+1)
        return sum(2*u**(2*j+1)/(2*j+1) for j in range(35))
    s=l(x)+k*l(Q(2))
    u=Q(1,3)
    return s,s+(k+1)*2*u**71/(71*(1-u*u))

def ei(x):
    req(1<=x<=Q(44))
    a,b=logi(x)
    t=Q(1);s=Q(0)
    for k in range(1,156):
        t*=x/k;s+=t/k
    return s+a+Q(577,1000),s+b+Q(578,1000)+t*x/(156*(156-x))

def p(n,l):
    return sum(Q(fac(k),1)/l**k for k in range(n+1))

def barrier(n,a,c):
    a=Q(a)
    P=p(n,a)/a
    e0,e1=expi(a)
    b0,b1=ei(a)
    req(b0/e1>P, 'lower barrier', n)
    req(b1/e0<P+c*fac(n+1)/a**(n+2), 'upper barrier', n)
    req(c*(1-Q(n+2)/a)>=1,'ode barrier',n)

def setup():
    # Gamma bracket from H_n - log n - 1/n < gamma < H_n - log n.
    a,b=logi(Q(4096)); h=sum(Q(1,k) for k in range(1,4097))
    req(Q(577,1000)<h-b-Q(1,4096)<h-a<Q(578,1000),'gamma')
    req(ei(Q(3))[1]*3< Q(3,2)*expi(Q(3))[0], 'global li upper')
    barrier(3,13,Q(3))
    barrier(20,26,Q(7))
    cs=[sum(fac(i)*comb(j,i)-fac(i)*fac(j-i) for i in range(j+1)) for j in range(21)]
    req(cs[:8]==[0,0,0,0,1,14,145,1412] and min(cs[8:])>0,cs)
    a=Q(26)
    tail=sum(sum(fac(i)*fac(j-i) for i in range(j-20,21))/a**(j-4) for j in range(21,41))
    delta=Q(7*fac(21),26**17)
    req(p(20,a)<Q(11,10) and tail+Q(11,5)*delta+delta**2<Q(1,1000),'base gap')
    req(p(20,Q(42))+Q(7*fac(21),42**21)<Q(21,20),'tail w')
    h=Q(42)
    c=1/(8*Q(314,100))
    v=c*h**5*(h-1)*expi((1-h)/2)[1]+Q(21,10)*c*h**6*expi(-h/2)[1]+c*c*h**8*expi(-h)[1]
    req(v<Q(62,100),'tail at 42',v)
    return v

def tables():
    path=Path('/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean')
    s=path.read_text().split('def table_2 :')[1]
    pat=r'\((?:(\d+) \* )?10 \^ (\d+), (-?[0-9.]+), (-?[0-9.]+)\)'
    r=[(int(m or 1)*10**int(n),Q(a),Q(b)) for m,n,a,b in re.findall(pat,s)]
    req(len(r)==31,len(r))
    return [(a,2*a,c,d) for a,c,d in r]+[(2,10**19,Q(-1),Q(1))]

def cover(rows,a,b,bound,upper):
    # Is [a,b] covered by the union of those closed row domains with
    # upper bound <= bound (or lower bound >= bound)?
    end=a
    reach=False
    for l,h,c,d in sorted(rows):
        if not (d<=bound if upper else c>=bound): continue
        if h>=a and l<=end:
            reach=True
            end=max(end,h)
            if end>=b:return True
    return reach and end>=b

def best(rows,a,b,upper):
    cand=sorted({r[3 if upper else 2] for r in rows},reverse=not upper)
    for value in cand:
        if cover(rows,a,b,value,upper):return value
    raise ValueError(('not covered',a,b))

def q(t):
    return Q(39,20)+Q(39,10)/t+Q(39,2)/t**2

def pp_lo(l,u):
    return p(3,u/2)-q(l/2)*expi(-l/4)[1]
def pp_hi(l):
    return p(3,l/2)+72/(l/2)**4+Q(3,2)*(
        sum(expi(-(Q(1,2)-Q(1,k))*l)[1] for k in range(3,11))+
        64*expi(-(Q(1,2)-Q(1,11))*l)[1])

def cell(rows, init, l, u, e0, e1):
    a,b=expi(l)[0],expi(u)[1]
    if b<init:
        return None  # mathematically empty after intersecting with x>=init
    a=max(a,init)
    # All calls to pp_* have 26<=log(t)<=42; in particular sqrt(t) lies
    # inside Buthe's stated range, and the total number of powers is <=64.
    c=max(Q(0),pp_lo(l,u)+best(rows,a,b,False))
    d=min(q(l-1),pp_hi(l-1)+best(rows,a/e1,b/e0,True))
    req(d>=0,'d nonnegative')
    fl=c*u**4*expi(-u/2)[0]
    fh=c*l**4*expi(-l/2)[1]
    eh=d*l**5/(l-1)*expi((1-l)/2)[1]
    B=1+14/u+145/u**2+1412/u**3-Q(1,1000)
    lower=down(B-eh+2*(1+1/u)*fl-fh**2/l**4)
    return (lower,l,c,d)

def grid(init=640000000000,step=Q(1,100)):
    rows=tables()
    e0,e1=expi(Q(1))
    init=Q(init)
    req(expi(Q(27))[1]<init,'log lower endpoint')
    data=[]
    l=Q(27)
    while l<42:
        u=min(l+step,42)
        rec=cell(rows,init,l,u,e0,e1)
        if rec is not None: data.append(rec)
        l=u
    globalmin=min(data)
    req(globalmin[0]>=Q(1,25),'grid minimum',globalmin)
    return len(data),globalmin

def bisect_cover(init=640000000000,target=Q(1,25)):
    # Never skip an undecided nonempty box. Failure at depth 20 is reported.
    init=Q(init)
    rows=tables()
    e0,e1=expi(Q(1))
    req(expi(Q(27))[1]<init, 'log lower endpoint')
    req(expi(Q(42))[1]<=10**19,'Buthe upper endpoint')
    req(64*logi(Q(2))[0]>42, 'power count')
    todo=[(Q(27),Q(42),0)]
    accepted=[]
    tested=0;skipped=0
    while todo:
        l,u,depth=todo.pop()
        result=cell(rows,init,l,u,e0,e1)
        tested+=1
        if result is None:
            skipped+=1
        elif result[0]>=target:
            accepted.append((l,u,result[0]))
        else:
            req(depth<20,'uncertified box',l,u,result)
            m=(l+u)/2
            todo.extend([(m,u,depth+1),(l,m,depth+1)])
    return tested,skipped,accepted

if __name__=='__main__':
    v=setup()
    tested,skipped,accepted=bisect_cover()
    print('adaptive log cells: tested',tested,'empty',skipped,'accepted',len(accepted))
    print('adaptive exact minimum:',min(v for _,_,v in accepted))
    i,data=grid()
    print('26 and 13 ODE barriers, degree 20 coefficients, square tail checked by exact rational arithmetic.')
    print('L>=42 uniform loss < 62/100; loss upper at 42 =',float(v))
    print('checked log cells:',i,'minimum rational enclosure:',data[0])
    print('minimum displayed:',float(data[0]),'first endpoint:',float(data[1]))
    print('min certified RG in cells >= 1/25')
