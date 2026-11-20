#!/usr/bin/env python3
"""Run the actual full finite target; numerical generation is UNTRUSTED.
All limits/commands/results are recorded. Certificate rows are 7 little-endian
uint64 words: start,next,j,Pupper,Q,logUpper,A. Cells are [start,next).
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, resource, subprocess, time

def main():
 p=argparse.ArgumentParser();p.add_argument('--study',type=pathlib.Path,required=True);p.add_argument('--scratch',type=pathlib.Path,required=True);p.add_argument('--end',type=int,default=1490000000000);p.add_argument('--chunks',type=int,default=64);p.add_argument('--workers',type=int,default=16);p.add_argument('--mode',choices=['actual','unit'],default='actual');a=p.parse_args()
 begin=38358837683; end=a.end+1
 if not (begin<end<=1620000000001 and 1<=a.chunks<=256 and 1<=a.workers<=16):raise ValueError('parameters')
 a.study=a.study.resolve();a.scratch=a.scratch.resolve()
 if not a.scratch.is_dir() or a.scratch.name!='ivy-ramanujan-source-pv-20261119':raise ValueError('scratch ownership')
 mem=dict((s.split(':')[0],int(s.split()[1])*1024) for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if ':' in s)
 stat=os.statvfs(a.scratch); free=stat.f_bavail*stat.f_frsize
 if mem['MemAvailable'] < 512*(1<<30) or free < 1024*(1<<30):raise RuntimeError('host reserve unavailable')
 root=a.study/'evidence'/('finite-'+a.mode+'-'+str(a.end));root.mkdir(exist_ok=False)
 certroot=a.scratch/('finite-'+a.mode+'-'+str(a.end));certroot.mkdir(exist_ok=False)
 manifest={'status':'RUNNING_UNTRUSTED_NUMERICAL_GENERATION','begin':begin,'end_inclusive':a.end,'mode':a.mode,'chunks':a.chunks,'workers':a.workers,'ram_limit_per_process':16*(1<<30),'host_mem_available_at_start':mem['MemAvailable'],'scratch_free_at_start':free,'formal_verification':False,'source_sha256':hashlib.sha256((a.study/'network/Solutions/RamanujanSourcePV.v1/c/generate_finite.cpp').read_bytes()).hexdigest(),'executable_sha256':hashlib.sha256((a.scratch/'generate_finite').read_bytes()).hexdigest()}
 (root/'RUN.json').write_text(json.dumps(manifest,indent=2)+'\n'); start=time.monotonic()
 def work(i):
  b=begin+(end-begin)*i//a.chunks;e=begin+(end-begin)*(i+1)//a.chunks
  cert=certroot/(str(i)+'.bin');cmd=[str(a.scratch/'generate_finite'),str(b),str(e),str(cert),a.mode]
  cpu=16+i%16
  def limits():
   resource.setrlimit(resource.RLIMIT_AS,(16<<30,16<<30));os.sched_setaffinity(0,{cpu})
  t=time.monotonic()
  with (root/(str(i)+'.stdout')).open('wb') as out,(root/(str(i)+'.stderr')).open('wb') as err:
   x=subprocess.run(['/usr/bin/time','-v','-o',str(root/(str(i)+'.rusage')),*cmd],stdout=out,stderr=err,preexec_fn=limits)
  h=hashlib.sha256()
  if cert.exists():
   with cert.open('rb') as f:
    for data in iter(lambda:f.read(8<<20),b''):h.update(data)
  rec={'chunk':i,'begin':b,'end_exclusive':e,'command':cmd,'exit_code':x.returncode,'wall_seconds':time.monotonic()-t,'certificate_bytes':cert.stat().st_size if cert.exists() else 0,'certificate_sha256':h.hexdigest() if cert.exists() else None}
  if x.returncode==0:rec['numeric_result']=json.loads((root/(str(i)+'.stdout')).read_text())
  (root/(str(i)+'.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'chunk':i,'exit_code':x.returncode,'seconds':rec['wall_seconds'],'bytes':rec['certificate_bytes']}),flush=True);return rec
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool: records=list(pool.map(work,range(a.chunks)))
 manifest.update(status='UNTRUSTED_NUMERICAL_GENERATION_COMPLETE' if all(x['exit_code']==0 for x in records) else 'GENERATION_FAILED',wall_seconds=time.monotonic()-start,records=records,certificate_bytes=sum(x['certificate_bytes'] for x in records))
 (root/'RUN.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k] for k in ['status','wall_seconds','certificate_bytes']}),flush=True)
 if manifest['status']=='GENERATION_FAILED':raise SystemExit(1)
if __name__=='__main__':main()
