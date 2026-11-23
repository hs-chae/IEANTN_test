#!/usr/bin/python3.10
"""Second finite analytic route: Table 1 + integrated spectral transfer, no Table 2.

Exact-rational implementation of prose proof. No native zero data or prime counts.
"""
from ram_cert import Q, comb, fac, re, Path, req, expi, ei, p, q, setup, best, barrier, down, logi

def tables_psi():
    s=(Path(__file__).resolve().parents[3]/'IEANTN/Nodes/Buthe/v1/Tables.lean').read_text()
    s=s.split('def table_1 :',1)[1].split('def table_2 :',1)[0]
    pat=r'\((?:(\d+) \* )?10 \^ (\d+), (-?[0-9.]+), (-?[0-9.]+)\)'
    r=[(int(m or 1)*10**int(n),Q(a),Q(b)) for m,n,a,b in re.findall(pat,s)]
    req(len(r)==31,len(r))
    return [(a,2*a,c,d) for a,c,d in r]+[(12,10**19,Q("-.94"),Q(".94"))]

def lo(x):return expi(x)[0]
def hi(x):return expi(x)[1]
coef=[sum(fac(i)*comb(j,i)-fac(i)*fac(j-i) for i in range(j+1)) for j in range(21)]

def eshift(l):
    return Q(".1386")/(l-6)+Q("14.44")*l*hi(-l/2)

def high_w(s,k):
    if k==2: return p(8,s)+5*fac(9)/s**9
    if k<=5: return min(Q(8,5),p(1,s)+6/s**2)
    return Q(8,5)

def lower_powers(l,u):
    value=p(8,u/2)-q(l/2)*hi(-l/4)
    for k in range(3,6):
        value+=lo(-(Q(1,2)-Q(1,k))*u)*max(Q(0),p(3,u/k)-q(l/k)*hi(-l/(2*k)))
    return value

def upper_powers(l):
    return sum(high_w(l/k,k)*hi(-(Q(1,2)-Q(1,k))*l) for k in range(2,11)) + Q(512,5)*hi(-(Q(1,2)-Q(1,11))*l)

def control():
    setup()
    barrier(8,13,Q(5))
    barrier(1,5,Q(3))
    req(ei(Q(5))[0]*5>p(3,Q(5))*hi(Q(5)),'low cube etc.')
    req(Q(".047")*(1+Q(16,26))<Q(".076"),'J error coeft')
    req(hi(Q(42))<=10**19, 'Buthe upper endpoint')
    req(64*logi(Q(2))[0]>42, 'power count')

def run(init=610000000000, target=Q(".001"), depth_cap=30):
    rows=tables_psi()
    lo_e,hi_e=expi(Q(1))
    req(hi(Q(27))<init,'log lower endpoint')
    stack=[(Q(27),Q(42),0)]
    accepted=[];empty=0;visited=0
    while stack:
        l,u,k=stack.pop()
        visited+=1
        a,b=max(lo(l),Q(init)),hi(u)
        if b<a:
            empty+=1;continue
        c=max(Q(0),best(rows,a,b,False)-eshift(l)+lower_powers(l,u))
        d=min(q(l-1),best(rows,a/hi_e,b/lo_e,True)+eshift(l-1)+upper_powers(l-1))
        req(d>=0)
        fl=c*u**4*lo(-u/2)
        fh=c*l**4*hi(-l/2)
        eh=d*l**5/(l-1)*hi((1-l)/2)
        B=sum(coef[j]/u**(j-4) for j in range(4,21))-Q(".001")
        # w(l) >= p_20(l) >= p_20(u), still retaining its sign.
        lower=down(B-eh+2*p(20,u)*fl-fh**2/l**4)
        if lower>=target:
            accepted.append((l,u,lower))
        else:
            req(k<depth_cap,'depth cap',float(l),float(u),float(lower))
            m=(l+u)/2
            stack.extend([(m,u,k+1),(l,m,k+1)])
    return visited,empty,len(accepted),min(x[2] for x in accepted)

if __name__=='__main__':
    control()
    for init in [610000000000,620000000000,630000000000,640000000000]:
        try:
            vals=run(init)
            print('passed',init,'visited, empty, accepted, minimum:',vals, float(vals[-1]))
        except ValueError as e:
            print('FAILED onset scouting control',init,e)
