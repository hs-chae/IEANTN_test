"""Search selected truncation/root-test settings, not domain sampling. Each reported winner is certified."""
from d02_cert import *
deal=[(4,0),(5,0),(5,".5"),(5,".9"),(5,".99"),(6,0),(7,0),(8,0),(10,0),(12,0),(14,0),
      (16,0),(17,0),(20,0),(24,0),(32,0),(48,0),(64,0),(100,0)]
s=D(".75")
if __name__=="__main__":
    for n,e in deal:
        for cap in [CAP0,CAP2]:
            best=None
            for m in [n+4,n+6,n+8,n+10]:
                for k in RT:
                    lo=max(10100,100*(2*(m+2)+1),int(100*((m+1)/slow(cap)+1))+1)
                    hi=max(lo+1,max(50000,5000*n)) if best is None else best[0]-1
                    if hi<=lo or compare(n,D(hi)/100,m,cap,s,k,e,False)>=1: continue
                    while hi-lo>1:
                        mid=(hi+lo)//2
                        if compare(n,D(mid)/100,m,cap,s,k,e,False)<1: hi=mid
                        else: lo=mid
                    if not best or hi<best[0]:
                        best=(hi,m,k)
            a,m,k=best
            compare(n,D(a)/100,m,cap,s,k,e)
