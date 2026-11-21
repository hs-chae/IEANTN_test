"""Exact scalar checks for all-real Johnston range, no grid and no new prime data."""
from ram_cert import Q, expi, logi, req, setup
def eup(x):
    return expi(Q(x)/3)[1]**3
def D(L,a):
    L=Q(L)
    return a*L**5*(L-1)*eup((1-L)/2)+Q(21,10)*a*L**6*eup(-L/2)+a*a*L**8*eup(-L)

setup()
T=3*10**12
ln59=logi(Q(59))[0]
req(Q('9.06')**2*eup(59)<=T*T*59*ln59**2,'Johnston Thm 3.2 admissibility')
req(D(42,1/(8*Q('3.141592')))<Q('.62'),'Schoenfeld-size first ray')
starts=[59,69,74,79,84,89,93,98]
ends=[69,74,79,84,89,93,98,103]
a=[10**k for k in range(8)]
K=list(map(Q,['1.19','.117','.0116','.00116','.000116','.0000116','.00000116','.000000116']))
print('Theorem 3.2: log x in [42,59]; strict normalized margin > .379.')
for l,u,b,k in zip(starts,ends,a,K):
    req(k*k*eup(u)<=T*T*u**3,'Johnston Thm 4.1 admissibility',u)
    val=D(l,b)
    req(val<Q('.025'),'tail loss',l,val)
    print('Theorem 4.1: closed height slab',l,u,'a',b,'loss upper',float(val))
print('Normalized margin > .974 across [59,103], using only 8 slab checks.')
