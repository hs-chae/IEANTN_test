#!/usr/bin/env python3
"""Untrusted demand-DAG workload measurement; successful return is not a proof."""
from pathlib import Path
import argparse,bisect,functools,hashlib,json,math,os,resource,sys,time

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--n',type=int,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--max-nodes',type=int,default=10000000);a=ap.parse_args()
    if not 2<=a.n<=2000000000000:raise ValueError('exact bounded input')
    if not 1<=a.max_nodes<=100000000:raise ValueError('finite declared node budget')
    if a.out.exists():raise ValueError('fresh owned result')
    os.sched_setaffinity(0,{0,1,2,3});resource.setrlimit(resource.RLIMIT_AS,(128*1024**3,128*1024**3));resource.setrlimit(resource.RLIMIT_STACK,(256*1024**2,256*1024**2));sys.setrecursionlimit(1000000)
    started=time.monotonic();root=math.isqrt(a.n);sieve=bytearray(b'\1')*(root+1);sieve[:2]=b'\0\0'
    for p in range(2,math.isqrt(root)+1):
        if sieve[p]:sieve[p*p:root+1:p]=b'\0'*((root-p*p)//p+1)
    primes=[p for p in range(2,root+1)if sieve[p]];updates=0;shortcuts=0
    class Budget(Exception):pass
    @functools.lru_cache(None)
    def pi(v):
        if v<4:return max(v-1,0)
        return after(bisect.bisect_right(primes,math.isqrt(v))-1,v)
    @functools.lru_cache(None)
    def after(k,v):
        nonlocal updates,shortcuts
        if after.cache_info().currsize+pi.cache_info().currsize>=a.max_nodes:raise Budget()
        if k<0:return max(v-1,0)
        p=primes[k]
        if v<p*p:
            shortcuts+=1
            return pi(v)
        av=after(k-1,v);bv=pi(p);cv=pi(p-1);dv=after(k-1,v//p)
        updates+=1
        result=av if bv==cv else av-(dv-cv)
        if result<0:raise ValueError('negative exact update')
        return result
    result=None;status='UNTRUSTED_DEMAND_DAG_SCOUT_ONLY'
    try:result=pi(a.n)
    except Budget:status='UNTRUSTED_DEMAND_DAG_NODE_BUDGET_EXHAUSTED_NO_FINAL_COUNT'
    record={'status':status,'N':a.n,'count':result,'true_arithmetic_updates':updates,'square_shortcuts':shortcuts,'after_states':after.cache_info().currsize,'pi_states':pi.cache_info().currsize,'node_budget':a.max_nodes,'seconds':time.monotonic()-started,'actual_peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seed':None,'qualification':'Untrusted workload scout; every eventual generated arithmetic/gap proof must be checked by Lean, and actual source correspondence remains separate.'}
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if __name__=='__main__':main()
