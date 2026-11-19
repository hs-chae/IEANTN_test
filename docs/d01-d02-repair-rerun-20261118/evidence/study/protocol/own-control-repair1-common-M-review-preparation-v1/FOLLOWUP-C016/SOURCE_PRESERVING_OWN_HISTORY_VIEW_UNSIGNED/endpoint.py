#!/usr/bin/python3.10
from cert import *
from subprocess import check_output
def atan(q):
    # Alternating rational series bracketing.
    p=sum(((-1)**n)*q**(2*n+1)/(2*n+1) for n in range(60))
    return I(I(p).a,I(p+q**121/121).b)
pi=16*atan(Q(1,5))-4*atan(Q(1,239))
assert I('3.14159265358979323846').b<pi.a and pi.b<I('3.14159265358979323847').a
assert (1/(2*pi)*(I(3000000000000)/(2*pi)).log()**2+I('1.8642')).b<117
assert (I(58)/2).exp().a>6*58
N=38358837682
e=I(1).exp()
assert (I(N)/e).a>D(14111427770)
assert (I(N+1)/e).b<D(14111427771)
output=check_output(['/work/pcount',str(N),str(N+1),'14111427770'],text=True)
assert list(map(int,output.split()))==[N,1644673232,N+1,1644673232,14111427770,632207037]
print(output,end='')
def gap(x):
    x=I(x)
    return e*x/x.log()*632207037-I(1644673232)**2
for s in ('0','0.217926365','0.217926366','1'):
    print('N + '+s,gap(N+Q(s)))
assert gap(N).b<0 and gap(N+1).a>0
assert gap(N+Q('0.217926365')).b<0 and gap(N+Q('0.217926366')).a>0
