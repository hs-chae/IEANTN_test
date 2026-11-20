#!/usr/bin/env python3
"""Deterministic native C/source association controls, not a new PV proof.

The generic Lean source execution theorems are independent. This small observer
compiles the unchanged C source and compares boundary and SplitMix64 queries
with the original exact integer algorithm, including near-uint64 denominators.
"""
from pathlib import Path
import argparse, hashlib, json, os, platform, re, resource, shutil, subprocess, sys, time
S=Path(__file__).resolve().parents[1]
F=1<<60
MASK=(1<<64)-1
SEED=0x51524852414D414E
STATUS='NATIVE_BOUNDARY_REGRESSION_OBSERVED_NO_NEW_PV_CLAIM'

def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def strict_json(path):
    def pairs(items):
        out={}
        for k,v in items:need(k not in out,'duplicate JSON key');out[k]=v
        return out
    def bad(x):raise ValueError('nonfinite JSON '+x)
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=bad)
def ceildiv(a,b):
    need(type(a)is int and type(b)is int and a>=0 and b>0,'exact ceil domain')
    return a//b+(0 if a%b==0 else 1)
def series(num,den):
    need(0<=num<1<<64 and 0<den<1<<64 and 2*num<=den,'series domain')
    z=ceildiv(F*num,den);z2=ceildiv(z*z,F);power=z;total=0
    for k in range(20):total+=ceildiv(power,2*k+1);power=ceildiv(power*z2,F)
    return 2*total+ceildiv(2*power*F,41*(F-z2))
def logarithm(n):
    need(2<=n<=2000000000000,'upper domain')
    two=1;k=0
    while two<=n//2:two*=2;k+=1
    return ceildiv(k*series(1,3)+series(n-two,n+two),1<<20)
def queries():
    q=[];seen=set()
    def add(kind,a,b=0):
        t=(kind,a,b)
        if t not in seen:seen.add(t);q.append(list(t))
    for k in range(1,41):
        for n in [(1<<k)-1,1<<k,(1<<k)+1]:
            if 2<=n<=2000000000000:add(0,n)
    for n in [38358837682,38358837683,38358837739,14111427770,38359837683,1490000000000,1999999999999,2000000000000]:add(0,n)
    state=SEED
    def rng():
        nonlocal state
        state=(state+0x9E3779B97F4A7C15)&MASK;z=state
        z=((z^(z>>30))*0xBF58476D1CE4E5B9)&MASK
        z=((z^(z>>27))*0x94D049BB133111EB)&MASK
        return z^(z>>31)
    for _ in range(128):add(0,2+rng()%1999999999999)
    for d in [1,2,3,4,5,(1<<31)-1,(1<<32)-1,(1<<63)-1,1<<63,(1<<64)-2,(1<<64)-1]:
        for n in [0,1,max(0,d//2-1),d//2]:
            if 2*n<=d:add(1,n,d)
    for _ in range(128):
        d=1+rng()%MASK;add(1,rng()%(d//2+1),d)
    return q

def expected(q):return [logarithm(a)if kind==0 else series(a,b)for kind,a,b in q]
def parse_output(path,count):
    lines=Path(path).read_text().splitlines();need(len(lines)==count,'every exact output line')
    out=[]
    for i,line in enumerate(lines):
        need(re.fullmatch(r'(0|[1-9][0-9]*)\t(0|[1-9][0-9]*)',line)is not None,'canonical output')
        a,b=map(int,line.split('\t'));need(a==i and 0<=b<1<<64,'exact output index/uint64');out.append(b)
    return out

def driver_source(q):
    driver='''#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n#include <limits.h>\n_Static_assert(sizeof(uint64_t)*CHAR_BIT==64,"uint64 width");\n_Static_assert(sizeof(__uint128_t)*CHAR_BIT==128,"uint128 width");\nuint64_t rpc_log_upper(uint64_t);\nuint64_t rpc_log_series_upper(uint64_t,uint64_t);\nstruct query { uint64_t kind,a,b; };\nstatic const struct query qs[]={\n'''
    driver+=',\n'.join('{UINT64_C(%d),UINT64_C(%d),UINT64_C(%d)}'%tuple(x)for x in q)
    driver+='''\n};\nint main(void){for(size_t i=0;i<sizeof(qs)/sizeof(qs[0]);++i){uint64_t x=qs[i].kind?rpc_log_series_upper(qs[i].a,qs[i].b):rpc_log_upper(qs[i].a);if(printf("%zu\\t%" PRIu64 "\\n",i,x)<0)return 2;}return fflush(stdout)==0?0:3;}\n'''
    return driver

def check(out,candidate=None):
    r=strict_json(out/'RESULT.json') if candidate is None else candidate;need(r['status']==STATUS,'complete native observation status')
    need(r['script_sha256']==sha(__file__),'current observer identity')
    need(r['seed']==SEED and r['generator']=='SplitMix64 constants in script','fixed seed/algorithm')
    q=queries();need(strict_json(out/'queries.json')==q,'exact fixed query universe')
    need(type(r['query_count'])is int and r['query_count']==len(q),'exact query count')
    names=['compile.json','compile.rusage','compile.stderr','compile.stdout','driver.c','expected.json','finite_log_observer','native.json','native.rusage','native.stderr','native.stdout','observer.py','queries.json','verified_finite_log.c']
    need([Path(x['path']).name for x in r['artifacts']]==names,'complete ordered artifact universe')
    for item in r['artifacts']:
        path=Path(item['path']);need(path==out/path.name and path.is_file(),'exact experiment artifact path')
        need(sha(path)==item['sha256'] and type(item['bytes'])is int and path.stat().st_size==item['bytes'],'artifact identity/length')
    need(sha(out/'observer.py')==sha(__file__),'executed observer snapshot')
    need(sha(out/'verified_finite_log.c')==r['actual_C_source_sha256'],'compiled source copy')
    need((out/'driver.c').read_text()==driver_source(q),'exact fixed caller source')
    need(strict_json(out/'compile.json')==r['compile'] and strict_json(out/'native.json')==r['execute'],'actual child receipts')
    for label,key in [('compile','compile'),('native','execute')]:
        child=r[key];need(type(child['returncode'])is int and child['returncode']==0,'actual integer exit status')
        measured=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(out/(label+'.rusage')).read_text())
        need(measured is not None and type(child['peak_rss_bytes'])is int and child['peak_rss_bytes']==int(measured[1])*1024,'actual RSS readback')
        need(child['memory_ceiling_bytes']==8<<30 and type(child['memory_ceiling_bytes'])is int,'recorded native ceiling')
        need(type(child['seconds'])in[int,float] and child['seconds']>=0,'measured duration')
    need(r['compile']['command']==[r['compiler'],'-std=c11','-O2','-Wall','-Wextra','-Werror','-Wno-empty-body',str(out/'verified_finite_log.c'),str(out/'driver.c'),'-o',str(out/'finite_log_observer')],'actual exact compile command')
    need(r['execute']['command']==[str(out/'finite_log_observer')],'actual executable invocation')
    need(sha(S/'c/verified_finite_log.c')==r['actual_C_source_sha256'],'unchanged original C source')
    need(sha(r['compiler'])==r['compiler_sha256'],'actual compiler bytes')
    need(r['compile']['returncode']==0 and r['execute']['returncode']==0,'actual successful child routes')
    need(r['compile']['oom_or_sigkill']is False and r['execute']['oom_or_sigkill']is False,'no native child kill')
    got=parse_output(out/'native.stdout',len(q));want=expected(q)
    need(got==want and strict_json(out/'expected.json')==want,'all exact integer reference outputs')
    need(r['new_PV_claim']is False and r['formal_proof_replay']is False,'native-only trust label')
    answer={'status':'CHECKED_NATIVE_BOUNDARY_OBSERVATION','queries':len(q)}
    if candidate is None:answer['result_sha256']=sha(out/'RESULT.json')
    return answer

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path);p.add_argument('--check',type=Path)
    p.add_argument('--compiler',default='gcc');p.add_argument('--cpu',type=int,default=19);a=p.parse_args()
    if a.check is not None:
        need(a.out is None,'check is a separate read-only mode');print(json.dumps(check(a.check.resolve()),sort_keys=True));return
    need(a.out is not None,'fresh --out required');out=a.out.resolve();need(not out.exists()and out.parent.is_dir(),'fresh output')
    compiler=shutil.which(a.compiler);need(compiler is not None,'actual C compiler')
    compiler=str(Path(compiler).resolve());need(a.cpu in os.sched_getaffinity(0),'actual CPU')
    available=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024
    need(available>(512+8)<<30,'host reserve plus small native8GiB ceiling')
    out.mkdir();source=S/'c/verified_finite_log.c';copy=out/'verified_finite_log.c';copy.write_bytes(source.read_bytes())
    q=queries();(out/'queries.json').write_text(json.dumps(q,indent=2)+'\n');(out/'expected.json').write_text(json.dumps(expected(q))+'\n')
    driver=driver_source(q)
    (out/'driver.c').write_text(driver);(out/'observer.py').write_bytes(Path(__file__).read_bytes())
    def limits():resource.setrlimit(resource.RLIMIT_AS,(8<<30,8<<30));os.sched_setaffinity(0,{a.cpu})
    def run(name,cmd):
        start=time.monotonic()
        with(out/(name+'.stdout')).open('wb')as so,(out/(name+'.stderr')).open('wb')as se:
            r=subprocess.run(['/usr/bin/time','-v','-o',str(out/(name+'.rusage')),*cmd],cwd=out,stdout=so,stderr=se,preexec_fn=limits)
        usage=(out/(name+'.rusage')).read_text();m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',usage)
        need(m is not None,'measured child RSS')
        record={'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-start,'peak_rss_bytes':int(m[1])*1024,'memory_ceiling_bytes':8<<30,'cpus':[a.cpu],'oom_or_sigkill':r.returncode in [-9,137]}
        (out/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n');need(r.returncode==0,'native child '+name+' failed');return record
    start=time.monotonic();exe=out/'finite_log_observer'
    compiled=run('compile',[compiler,'-std=c11','-O2','-Wall','-Wextra','-Werror','-Wno-empty-body',str(copy),str(out/'driver.c'),'-o',str(exe)])
    executed=run('native',[str(exe)])
    need(parse_output(out/'native.stdout',len(q))==expected(q),'compiled C exact reference mismatch')
    record={'status':STATUS,'script_sha256':sha(__file__),'seed':SEED,'generator':'SplitMix64 constants in script','query_count':len(q),'log_queries':sum(x[0]==0 for x in q),'series_queries':sum(x[0]==1 for x in q),'new_PV_claim':False,'formal_proof_replay':False,'actual_C_source':str(source),'actual_C_source_sha256':sha(source),'compiler':compiler,'compiler_sha256':sha(compiler),'compiler_version':subprocess.check_output([compiler,'--version'],text=True),'compiler_target':subprocess.check_output([compiler,'-dumpmachine'],text=True).strip(),'python':sys.version,'python_optimization':sys.flags.optimize,'platform':platform.platform(),'compile':compiled,'execute':executed,'seconds':time.monotonic()-start,'host_memavailable_before_bytes':available,'host_reserve_bytes':512<<30,'artifacts':[]}
    for f in sorted(out.iterdir()):
        if f.is_file():record['artifacts'].append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
    record['experiment_owned_disk_bytes_before_result']=sum(x['bytes']for x in record['artifacts'])
    check(out,record)
    tmp=out/'RESULT.json.tmp';tmp.write_text(json.dumps(record,indent=2)+'\n');tmp.replace(out/'RESULT.json')
    print(json.dumps(check(out),sort_keys=True))
if __name__=='__main__':main()
