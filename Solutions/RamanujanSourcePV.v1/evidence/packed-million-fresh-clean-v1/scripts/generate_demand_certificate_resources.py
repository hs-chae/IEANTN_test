#!/usr/bin/env python3
"""Resource-parameterized counterpart of the immutable demand-DAG proposer. Lean validates every gap and row.

Output is a fresh experiment-owned source tree. Large regenerable literals stay
outside the publication checkout. Native proposal values are never proof input
axioms; all checked chunks and the final theorem must actually compile.
"""
from pathlib import Path
import argparse,bisect,functools,hashlib,json,math,os,re,resource,shutil,sys,time
WIDTHS=(2,22,42,42,32,32,32,32,22,22,22,22)
HEADER='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def pack(row):
    total=0;shift=0
    for value,width in zip(row,WIDTHS):
        need(type(value)is int and 0<=value<1<<width,'exact bounded packed field')
        total|=value<<shift;shift+=width
    return total

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--queries',required=True);ap.add_argument('--name',required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--data-chunk',type=int,default=131072);ap.add_argument('--proof-chunk',type=int,default=32768)
    ap.add_argument('--max-records',type=int,default=100000000)
    ap.add_argument('--cpus',default='0,1,2,3')
    ap.add_argument('--memory-gib',type=int,default=128)
    a=ap.parse_args()
    cpus=[int(x) for x in a.cpus.split(',')]
    need(cpus and len(cpus)==len(set(cpus)) and set(cpus)<=os.sched_getaffinity(0),'available unique CPU affinity')
    need(16<=a.memory_gib<=300,'owner per-run memory allowance')
    meminfo=dict((row.split(':')[0],int(row.split(':')[1].split()[0])*1024) for row in Path('/proc/meminfo').read_text().splitlines() if ':' in row and row.split(':')[1].strip().split() and row.split(':')[1].strip().split()[0].isdigit())
    need(meminfo['MemAvailable']>=1024**4 and meminfo['MemAvailable']>=((512+a.memory_gib)*1024**3),'genuinely available memory and host reserve')
    need(shutil.disk_usage(a.out.resolve().parent).free>=1024**4,'independent free disk allowance')
    queries=[int(x)for x in a.queries.split(',')]
    need(queries and len(queries)==len(set(queries))and all(2<=n<=2000000000000 for n in queries),'distinct exact query universe')
    need(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',a.name)is not None,'safe exact Lean namespace')
    need(1<=a.data_chunk<=1048576 and 1<=a.proof_chunk<=1048576,'bounded declared chunks')
    need(1<=a.max_records<=300000000,'finite record budget')
    out=a.out.resolve();need(not out.exists(),'fresh owned output');out.mkdir(parents=True)
    os.sched_setaffinity(0,set(cpus));resource.setrlimit(resource.RLIMIT_AS,(a.memory_gib*1024**3,a.memory_gib*1024**3));resource.setrlimit(resource.RLIMIT_STACK,(256*1024**2,256*1024**2));sys.setrecursionlimit(1000000)
    started=time.monotonic();maximum=max(queries);root=math.isqrt(maximum);spf=list(range(root+1));primes=[]
    for p in range(2,root+1):
        if spf[p]==p:
            primes.append(p)
            for k in range(p*p,root+1,p):
                if spf[k]==k:spf[k]=p
    gaps=[];gap_by_first={};previous=2
    for p in [*primes,root+1]:
        if p<previous:continue
        factors=[spf[k]for k in range(previous,p)]
        need(all(2<=d<k and k%d==0 for k,d in zip(range(previous,p),factors)),'complete proposed composite gap')
        gap_by_first[previous]=len(gaps);gaps.append((previous,p,factors));previous=p+1
    rows=[];updates=0;finishes=0
    def append(row):
        need(len(rows)<a.max_records,'declared record budget exhausted')
        packed=pack(row);i=len(rows);rows.append((row,packed))
        if len(rows)%1000000==0:
            progress={'status':'UNTRUSTED_HIGH_ENDPOINT_PROPOSAL_GENERATION','records':len(rows),'seconds':time.monotonic()-started,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'queries':queries,'max_records':a.max_records,'cpus':cpus,'memory_gib':a.memory_gib}
            temp=out/'PROGRESS.json.pending';temp.write_text(json.dumps(progress,indent=2)+'\n');temp.replace(out/'PROGRESS.json')
        return i
    @functools.lru_cache(None)
    def base(v):return append((0,2,v,max(v-1,0),0,0,0,0,0,0,0,0))
    def value(i):return rows[i][0][3]
    def gap_for(i,stage):
        row=rows[i][0]
        if row[0]==2:
            need(row[2]<stage*stage,'final-cell reference domain');return 0
        if row[1]==stage:return 0
        gid=gap_by_first[row[1]];first,last,_=gaps[gid]
        need(first==row[1] and first<=stage<=last,'actual proposed composite-gap edge');return gid
    @functools.lru_cache(None)
    def pi(v):
        nonlocal finishes
        if v<4:source=base(v);frontier=2
        else:
            k=bisect.bisect_right(primes,math.isqrt(v))-1
            source=after(k,v);frontier=math.isqrt(v)+1
        need(rows[source][0][2]==v,'exact argument identity')
        gid=gap_for(source,frontier);finishes+=1
        return append((2,frontier,v,value(source),source,0,0,0,gid,0,0,0))
    @functools.lru_cache(None)
    def after(k,v):
        nonlocal updates
        if k<0:return base(v)
        p=primes[k]
        if v<p*p:return pi(v)
        ia=after(k-1,v);ib=pi(p);ic=pi(p-1);id=after(k-1,v//p)
        av,bv,cv,dv=map(value,[ia,ib,ic,id]);result=av if bv==cv else av-(dv-cv)
        need(result>=0,'nonnegative proposed update');updates+=1
        return append((1,p+1,v,result,ia,ib,ic,id,gap_for(ia,p),gap_for(ib,p),gap_for(ic,p),gap_for(id,p)))
    results=[]
    for n in queries:
        i=pi(n);results.append({'N':n,'index':i,'value':value(i),'entry':list(rows[i][0])})
    generation_seconds=time.monotonic()-started;source_root=out/'source';folder=source_root/'RamanujanPV'/a.name;folder.mkdir(parents=True)
    namespace='RamanujanPV.'+a.name;modules=[]
    def finish_file(path,module,kind,deps):
        modules.append({'module':module,'kind':kind,'source':str(path),'source_root':str(source_root),'sha256':sha(path),'bytes':path.stat().st_size,'dependencies':deps})
    def write_tree(f,lo,hi,leaf):
        if hi-lo==1:f.write('(.leaf '+leaf(lo)+')');return
        mid=(lo+hi)//2;f.write(f'(.branch {mid} ');write_tree(f,lo,mid,leaf);f.write(' ');write_tree(f,mid,hi,leaf);f.write(')')
    packed_file=out/'records.324bit.le';h=hashlib.sha256()
    with packed_file.open('wb')as f:
        for row,word in rows:
            raw=word.to_bytes(41,'little');f.write(raw);h.update(raw)
    data_parts=[]
    for part,lo in enumerate(range(0,len(rows),a.data_chunk)):
        hi=min(lo+a.data_chunk,len(rows));short=f'Data{part:04d}';module=namespace+'.'+short;path=folder/(short+'.lean');name=f'raw_{part:04d}'
        with path.open('w')as f:
            f.write(HEADER+'import Lean.Data.RArray\nnamespace '+namespace+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nnoncomputable def '+name+' : Lean.RArray Nat := ')
            write_tree(f,lo,hi,lambda i:'0x'+format(rows[i][1],'x'));f.write('\nend '+namespace+'\n')
        finish_file(path,module,'data',[]);data_parts.append((lo,hi,module,name))
    gap_path=folder/'Gaps.lean';gap_module=namespace+'.Gaps'
    with gap_path.open('w')as f:
        f.write(HEADER+'import RamanujanPV.QuotientCertificateCode\nnamespace '+namespace+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nnoncomputable def gaps : Lean.RArray Gap := ')
        write_tree(f,0,len(gaps),lambda i:'⟨'+str(gaps[i][0])+','+str(gaps[i][1])+',['+','.join(map(str,gaps[i][2]))+']⟩')
        f.write('\ndef gapCount : Nat := '+str(len(gaps))+'\nend '+namespace+'\n')
    finish_file(gap_path,gap_module,'data',['RamanujanPV.QuotientCertificateCode'])
    data_path=folder/'Data.lean';data_module=namespace+'.Data'
    def merge_parts(lo,hi):
        if hi-lo==1:return data_parts[lo][3]
        mid=(lo+hi)//2;return f'(.branch {data_parts[mid][0]} '+merge_parts(lo,mid)+' '+merge_parts(mid,hi)+')'
    with data_path.open('w')as f:
        f.write(HEADER+'import RamanujanPV.QuotientCertificateCode\nimport '+gap_module+'\n'+''.join('import '+part[2]+'\n'for part in data_parts)+'namespace '+namespace+'\nopen QuotientDemandCheck QuotientPackedDemand\n')
        f.write('noncomputable def rawNodes : Lean.RArray Nat := '+merge_parts(0,len(data_parts))+'\nnoncomputable def nodes : Lean.RArray Entry := unpack rawNodes\ndef entryCount : Nat := '+str(len(rows))+'\nend '+namespace+'\n')
    finish_file(data_path,data_module,'data',['RamanujanPV.QuotientCertificateCode',gap_module,*[p[2]for p in data_parts]])
    gap_check_path=folder/'GapCheck.lean';gap_check_module=namespace+'.GapCheck'
    gap_check_path.write_text(HEADER+'import '+data_module+'\nnamespace '+namespace+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem gaps_checked : checkGaps gaps gapCount=true := by decide +kernel\n#print axioms gaps_checked\nend '+namespace+'\n')
    finish_file(gap_check_path,gap_check_module,'check',[data_module])
    proof_parts=[]
    for part,lo in enumerate(range(0,len(rows),a.proof_chunk)):
        size=min(a.proof_chunk,len(rows)-lo);short=f'Check{part:04d}';module=namespace+'.'+short;path=folder/(short+'.lean');name=f'part_{part:04d}'
        path.write_text(HEADER+'import '+data_module+'\nnamespace '+namespace+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem '+name+' : allFrom (checkEntry nodes gaps gapCount) '+str(lo)+' '+str(size)+'=true := by decide +kernel\n#print axioms '+name+'\nend '+namespace+'\n')
        finish_file(path,module,'check',[data_module]);proof_parts.append((lo,size,module,name))
    final_path=folder/'Final.lean';final_module=namespace+'.Final'
    final=HEADER+'import RamanujanPV.QuotientDemandCheck\nimport '+gap_check_module+'\n'+''.join('import '+p[2]+'\n'for p in proof_parts)+'namespace '+namespace+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
    for part,(lo,size,module,name)in enumerate(proof_parts):
        if part==0:final+='theorem union_0000 : allFrom (checkEntry nodes gaps gapCount) 0 '+str(size)+'=true := '+name+'\n'
        else:
            total=lo+size
            final+=f'theorem union_{part:04d} : allFrom (checkEntry nodes gaps gapCount) 0 {total}=true := allFrom_append_checked (i:=0) (n:={lo}) (m:={size}) union_{part-1:04d} {name}\n'
    final+='theorem entries_checked : checkEntries nodes gaps gapCount entryCount=true := union_'+str(len(proof_parts)-1).zfill(4)+'\n'
    for result in results:
        n,i,val,row=result['N'],result['index'],result['value'],result['entry'];literal='⟨'+','.join(map(str,row))+'⟩'
        final+=f'theorem root_{n} : nodes.get {i}={literal} := by decide +kernel\n'
        final+=f'theorem pi_{n} : Nat.primeCounting {n}={val} := by\n  have h:=certificate_pi (i:={i}) gaps_checked entries_checked (by decide) (by simpa only [root_{n}] using (show ({row[0]}:Nat)=2 by decide))\n  simpa only [root_{n}] using h\n#print axioms pi_{n}\n'
    final+='end '+namespace+'\n';final_path.write_text(final);finish_file(final_path,final_module,'final',['RamanujanPV.QuotientDemandCheck',gap_check_module,*[p[2]for p in proof_parts]])
    manifest={'schema':'RAMANUJAN_PACKED_DEMAND_CERTIFICATE_PROPOSAL_V1','status':'UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','namespace':namespace,'queries':queries,'results':results,'records':len(rows),'arithmetic_updates':updates,'finished_pi_records':finishes,'gaps':len(gaps),'packed_widths':list(WIDTHS),'packed_bits':sum(WIDTHS),'packed_bytes_per_record':41,'packed_file':str(packed_file),'packed_sha256':h.hexdigest(),'packed_bytes':packed_file.stat().st_size,'data_chunk':a.data_chunk,'proof_chunk':a.proof_chunk,'source_root':str(source_root),'modules':modules,'final_module':final_module,'generator_sha256':sha(__file__),'algorithm_parent_generator_sha256':'c4b2b794fccb870af367ebed042cd256c35d91aadc5d7b90ad20487a4e209eda','resource_only_variant':True,'cpus':cpus,'memory_gib':a.memory_gib,'seed':None,'generation_seconds':generation_seconds,'total_seconds':time.monotonic()-started,'actual_peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'qualification':'The prime list, arithmetic rows, tree construction and Python proposer are untrusted. GapCheck and every Check module must compile; Final proves the actual prime-count conclusions from these completed kernel checks. This is ordinary kernel certificate arithmetic; it contributes to source-first PV only through a separately completed actual C source/AST/execution/output/application proof.'}
    temporary=out/'PROPOSAL.json.pending';temporary.write_text(json.dumps(manifest,indent=2)+'\n');temporary.replace(out/'PROPOSAL.json')
    print(json.dumps({k:manifest[k]for k in ['status','queries','results','records','arithmetic_updates','gaps','generation_seconds','total_seconds','actual_peak_rss_bytes','packed_bytes','source_root','final_module']},indent=2))
if __name__=='__main__':main()
