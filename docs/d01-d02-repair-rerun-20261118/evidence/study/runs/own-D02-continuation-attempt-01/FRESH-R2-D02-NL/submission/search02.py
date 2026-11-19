
from gap02 import *
def mink(lo,hi,test):
    if test(lo):return lo
    assert test(hi)
    while hi-lo>1:
        m=(hi+lo)//2
        if test(m):hi=m
        else:lo=m
    return hi
A,C,Z=model(106)
if __name__=='__main__':
 cap=F(sys.argv[1])
 for n in (3,4,5,6,8,10,13,16,20,24,32,40,56,72,96):
    N=max(n+8,20)
    j=mink(1750,(70*n+300)*10,lambda L:tail(F(L,10),N,Z[:n],cap))
    print('ORDER',cap,n,N,F(j,10),flush=True)
 for p in ([1,14,140],[1,14,145],[1,14,145,1300],[1,14,145,1412],[1,14,145,1412,13000]):
    j=mink(1750,5000,lambda L:tail(F(L,10),20,p,cap))
    print('COEFFICIENT',cap,p,F(j,10),flush=True)
