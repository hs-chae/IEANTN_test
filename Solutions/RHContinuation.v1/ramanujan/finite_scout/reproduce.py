#!/usr/bin/env python3
"""Full remaining-domain native scout and deterministic row/query compression.
UNVERIFIED numerical data: no claim this proves prime counts or source-first PV.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,struct,time,os
S=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--vendor',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--twice',action='store_true');a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(p,j):
 t=p.with_suffix('.pending');t.write_text(json.dumps(j,indent=2)+'\n');os.replace(t,p)
O=a.out.resolve();need(not O.exists(),'fresh output');O.mkdir(parents=True);v=a.vendor.resolve();b=a.build.resolve();src=S/'generate_finite.cpp';cmd=['g++','-std=c++17','-O3','-fopenmp','-I'+str(v/'include'),'-I'+str(v/'lib/primesieve/include'),str(src),str(b/'libprimecount.a'),str(b/'lib/primesieve/libprimesieve.a'),'-lpthread','-o',str(O/'generate_finite')];r=subprocess.run(cmd,text=True,capture_output=True);(O/'compile.stdout').write_text(r.stdout);(O/'compile.stderr').write_text(r.stderr);need(r.returncode==0,'C++ compile')
start=time.monotonic();j={'status':'RUNNING_NATIVE_FULL_REMAINING_SCOUT','source_first_PV':False,'begin':38359837684,'end_exclusive':640000000000,'source_sha256':sha(src),'compiler_version':subprocess.run(['g++','--version'],capture_output=True,text=True).stdout,'compile_command':cmd,'vendor_commit':subprocess.run(['git','-C',str(v),'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip(),'primesieve_commit':subprocess.run(['git','-C',str(v/'lib/primesieve'),'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip(),'libraries':[{'path':str(q),'sha256':sha(q)}for q in[b/'libprimecount.a',b/'lib/primesieve/libprimesieve.a']],'runs':[]};save(O/'RESULT.json',j)
for k in range(2 if a.twice else 1):
 cert=O/('certificate-'+str(k)+'.bin');res=O/('run-'+str(k)+'.resources');cmd=[str(O/'generate_finite'),str(j['begin']),str(j['end_exclusive']),str(cert),'actual'];t=time.monotonic();r=subprocess.run(['/usr/bin/time','-v','-o',str(res),*cmd],capture_output=True,text=True);(O/('run-'+str(k)+'.stdout')).write_text(r.stdout);(O/('run-'+str(k)+'.stderr')).write_text(r.stderr);need(r.returncode==0,'native full-domain generation');num=json.loads(r.stdout);need(num['status']=='UNTRUSTED_NUMERICAL_FINITE_COVERAGE','status');need(num['begin']==j['begin']and num['end_exclusive']==j['end_exclusive'],'domain');need(cert.stat().st_size==56*num['cells'],'record count');digest=sha(cert);j['runs'].append({'returncode':r.returncode,'seconds':time.monotonic()-t,'certificate_sha256':digest,'bytes':cert.stat().st_size,'native_result':num,'command':cmd});save(O/'RESULT.json',j)
 if k:need(j['runs'][0]['certificate_sha256']==digest,'deterministic full regeneration failed')
# Streaming independent integer sanity and exact query census, not prime verification.
queries=set();last=j['begin'];count=0;lastP=lastQ=0
F=1<<60;term=total=F
for k in range(1,21):term//=k;total+=term
with(O/'certificate-0.bin').open('rb')as f:
 while True:
  raw=f.read(56)
  if not raw:break
  need(len(raw)==56,'truncated row');n,nxt,q,P,Q,lu,A=struct.unpack('<7Q',raw);need(n==last and n<nxt<=j['end_exclusive'],'full gap-free adjacency');need(q==n*F//(total+22),'directed e query');need(A==n*total//lu and (1<<20)*P*P<A*Q,'strict integer cell');need(P>=lastP and Q>=lastQ,'count order');queries.add(nxt-1);queries.add(q);last=nxt;lastP=P;lastQ=Q;count+=1
need(last==j['end_exclusive']and count==j['runs'][0]['native_result']['cells'],'complete exact stream');qh=hashlib.sha256();ordered=sorted(queries)
for q in ordered:qh.update(struct.pack('<Q',q))
j.update(status='COMPLETE_UNVERIFIED_NATIVE_FULL_DOMAIN_SCOUT',seconds=time.monotonic()-start,rows=count,unique_required_count_queries=len(queries),query_set_sha256=qh.hexdigest(),minimum_query=ordered[0],maximum_query=ordered[-1],source_first_PV_remaining='Actual primality/prime-count truth of all directed endpoint queries and source-model realization of the streaming checker remain unproved. Structural/integer checks are not ordinary certificate promotion or PV.',deterministic_full_regeneration_checked=a.twice)
# Both large outputs are deterministic and hash-identical. Remove only these
# experiment-owned regenerable files after both full runs and stream validation.
if a.twice:
 j['cleanup']=[{'path':str(O/('certificate-'+str(k)+'.bin')),'sha256':sha(O/('certificate-'+str(k)+'.bin')),'bytes':(O/('certificate-'+str(k)+'.bin')).stat().st_size,'reason':'exact regeneration checked by two full runs; source, parameters, receipts and hashes retained'}for k in range(2)]
 for row in j['cleanup']:
  q=Path(row['path']);need(q.parent==O and q.name in ['certificate-0.bin','certificate-1.bin'],'cleanup ownership');need(sha(q)==row['sha256'],'cleanup target hash');q.unlink()
 save(O/'CLEANUP.json',{'status':'COMPLETE_CHECKED_REGENERABLE_OWNED_OUTPUT_CLEANUP','targets':j['cleanup']})
save(O/'RESULT.json',j);print(json.dumps({k:j[k]for k in['status','rows','unique_required_count_queries','seconds','deterministic_full_regeneration_checked']}))
