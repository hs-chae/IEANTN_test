#!/usr/bin/env python3
"""Exhaustively check all prime counts with a separate, unverified byte sieve.
This is stronger numerical evidence but is explicitly NOT source-first PV.
"""
from numerical_records import load,validate,atomic_json
import argparse, concurrent.futures, hashlib, json, os, pathlib, resource, subprocess, time

def main():
 p=argparse.ArgumentParser();p.add_argument('--study',type=pathlib.Path,required=True);p.add_argument('--scratch',type=pathlib.Path,required=True);p.add_argument('--run',required=True);p.add_argument('--workers',type=int,default=16);a=p.parse_args();a.study=a.study.resolve();a.scratch=a.scratch.resolve()
 if not (1<=a.workers<=16 and a.scratch.name=='ivy-ramanujan-source-pv-20261119'):raise ValueError('bounds')
 source=a.study/'evidence'/a.run;run=load(source/'RUN.json')
 if run['status']!='UNTRUSTED_NUMERICAL_GENERATION_COMPLETE':raise ValueError('incomplete generator')
 validate(run,a.scratch,pathlib.Path(__file__).resolve().parents[1])
 o=a.study/'evidence'/(a.run+'-independent-v2');o.mkdir(exist_ok=False);start=time.monotonic()
 def work(rec):
  i=rec['chunk'];cert=a.scratch/a.run/(str(i)+'.bin');h=hashlib.sha256(cert.read_bytes()).hexdigest()
  if h!=rec['certificate_sha256']:raise ValueError('input hash')
  cmd=[str(a.scratch/'independent_finite_check'),str(cert),str(rec['begin']),str(rec['end_exclusive']),run['mode']]
  def limits():
   resource.setrlimit(resource.RLIMIT_AS,(32<<30,32<<30));os.sched_setaffinity(0,{32+i%16})
  t=time.monotonic()
  with (o/(str(i)+'.stdout')).open('wb') as out,(o/(str(i)+'.stderr')).open('wb') as err:x=subprocess.run(['/usr/bin/time','-v','-o',str(o/(str(i)+'.rusage')),*cmd],stdout=out,stderr=err,preexec_fn=limits)
  result={'chunk':i,'command':cmd,'exit_code':x.returncode,'wall_seconds':time.monotonic()-t,'certificate_sha256':h,'formal_verification':False}
  if not x.returncode:result['numerical_result']=load(o/(str(i)+'.stdout'))
  (o/(str(i)+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['chunk','exit_code','wall_seconds']}),flush=True);return result
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:records=list(pool.map(work,run['records']))
 result={'status':'INDEPENDENT_ORDINARY_EXHAUSTIVE_CHECK_PASS' if all(x['exit_code']==0 for x in records) else 'FAILED','wall_seconds':time.monotonic()-start,'formal_verification':False,'generator_run_sha256':hashlib.sha256((source/'RUN.json').read_bytes()).hexdigest(),'verifier_source_sha256':hashlib.sha256((a.study/'network/Solutions/RamanujanSourcePV.v1/c/independent_finite_check.cpp').read_bytes()).hexdigest(),'records':records}
 atomic_json(o/'RESULT.json',result);print(json.dumps({k:result[k] for k in ['status','wall_seconds','formal_verification']}),flush=True)
 if result['status']=='FAILED':raise SystemExit(1)
if __name__=='__main__':main()
