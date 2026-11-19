from verify import I, log, D
from pathlib import Path
W=1<<58
def floor(t):
 v=t.a*W//D
 assert t.b*W<(v+2)*D
 return v
N=2**18
tot=sum(W//i for i in range(1,N+1))
en=log(N)
# H_N-log N - 1/(2N) <= gamma <= same +1/N^2.
lo=tot-(-(-en.b*W//D))-W//(2*N)
hi=tot+N-floor(en)-W//(2*N)+W//N**2
print(lo,hi)
for j in range(256):print(floor(log(I(256+j)/256)))
print(floor(log(2)))
