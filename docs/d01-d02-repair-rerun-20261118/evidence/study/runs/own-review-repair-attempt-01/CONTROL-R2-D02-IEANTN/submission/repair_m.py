#!/usr/bin/python3.10
from pathlib import Path
from subprocess import run
from cert import *

F=2**62
K=10**8
Y=10**13
old=Path(__file__).with_name('sieve_receipt.txt').read_text().splitlines()
rows=[ls.split() for ls in old if ls.startswith('form 1 ')]
pairs=sorted({(int(r[7]),int(r[10])) for r in rows})
src=''.join(f'{a} {b}\n' for a,b in pairs)
read=run(['/work/repair_m'],input=src,encoding='ascii',capture_output=True,check=True).stdout.splitlines()
data=[tuple(map(int,s.split())) for s in read[:-1]]
assert [s[:2] for s in data]==pairs
counts={a:(s,k) for a,b,s,k in data}
n,r,s=read[-1].split()
assert n=='S_powers_100m'
power=I(Q(int(r),2**100)).a,I(Q(int(s),2**100)).b

# Compute the original gamma enclosure anew, without trusting decimal input.
# Bound log(n) at full interval precision instead of using the old logscaled.
n=10**6
h=sum(F//j for j in range(1,n+1))
g=I(I(Q(h,F)).a,I(Q(h+n,F)).b)-I(n).log()-I(Q(1,2*n))
g+=I(I(Q(-1,(n-1)**2)).a,I(Q(1,(n-1)**2)).b)
print('gamma interval',g)

# Main integral: pointwise finite geometric expansion of 1/(h+u),
# with alternating remainder in the direction of the first omitted term.
v=I(K).log()
def partial(n):
    return sum((-1)**j*factorial(j)/v**(j+1) for j in range(n))/(2*K)
J=I(partial(14).a,partial(15).b)
B=J*I(1,(1+I(Q(2,3*(K-1)))).b)
# g(t) <= (1+2/(3(K-1)))/(2 t^2 log t) on t>=K.
def gt(t):
    return (1+I(Q(2,3*(K-1))))/(2*I(t)**2*I(t).log())
eps=I('.000188')
eps2=I('.001')
assert (I('1.791000147')/I(K)**Q(1,2)+I('1.78')/I(K)**Q(2,3)).b<eps.a
assert (I('20.83')/I(Y).log()**3).b<eps2.a
pad=eps*(2*K*gt(K)+B)+eps2*(Y*gt(Y)+gt(Y)*Y)
T=B+I(pad.b.copy_negate(),pad.b)
M=g-I(*power)-T
print('prime power sum to K',I(*power))
print('main integral',B,'tail correction cap',pad.b)
print('M interval',M)
# Also check the earlier printed values, then find new milligrid starts.
out={}
for r in rows:
    ab=Q(r[3]); a,b,x=int(r[7]),int(r[10]),int(r[-1])
    s,k=counts[a]
    sp=I(I(Q(s,F)).a,I(Q(s+k,F)).b)
    def at(z):
        l=I(Q(z,1000)).log()
        tol=I(ab)/l**3
        return sp-M-l.log(),tol
    def yes(z):
        f,t=at(z)
        return f.b<=t.a and -f.a<=t.a
    assert 1000*a<=x<=1000*b and yes(x)
    l,u=1000*a,x
    while l<u:
        mid=(l+u)//2
        if yes(mid):u=mid
        else:l=mid+1
    assert yes(u)
    out[ab]=u
    print('reciprocal',str(ab),a,b,'old',x,'new',u)
for c,prose in [('0.2',2278382186),('0.15',5001781860),('0.12',8789120961)]:
    assert out[Q(c)]<=prose
