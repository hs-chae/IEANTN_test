#!/usr/bin/env python3
"""Additive common service repair: accept exact published helper kind/value schema.

Every replaced retrieval failure is retained byte-for-byte under HISTORY. No
mathematical outcome, source statement, worker context, or eligible paper changes.
"""
from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,os,re,time
P=Path(__file__).with_name('source_broker.py');PIN='91181a79fccad2c02035ada3bca7a543916f8be0ffc53fa335c8838edfeea2e3'
if hashlib.sha256(P.read_bytes()).hexdigest()!=PIN:raise RuntimeError('pinned original source broker changed')
s=importlib.util.spec_from_file_location('rh_original_source_broker',P);b=importlib.util.module_from_spec(s);s.loader.exec_module(b)
def normalized(req):
 if not isinstance(req,dict):raise ValueError('request must be object')
 r=dict(req)
 if 'value'in r:
  value=r['value'];kind=r.get('kind')
  if kind=='search':r['query']=value
  elif kind in ('url','fetch'):r['url']=value
  else:raise ValueError('unsupported typed source request')
 if not isinstance(r.get('id'),str)or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,79}',r['id']):raise ValueError('invalid request ID')
 if bool(r.get('query'))==bool(r.get('url')):raise ValueError('exactly one query or canonical URL required')
 return r
def handle(arm,raw):
 req=normalized(raw);folder=b.D/'literature'/arm/'admissions'/req['id'];receipt=folder/'RECEIPT.json';oldpin=None
 if receipt.exists():
  old=b.read(receipt)
  if old.get('request')==req:return old
  # Only the demonstrated exact schema failure may be repaired in place as a new retrieval attempt.
  if old.get('request')==raw and old.get('error')=='source request needs url or query':
   original=receipt.read_bytes();history=folder/'HISTORY/RECEIPT_INITIAL_V1.json';history.parent.mkdir(parents=True,exist_ok=True)
   if history.exists()and history.read_bytes()!=original:raise RuntimeError('historical failure differs')
   if not history.exists():history.write_bytes(original)
   oldpin={'path':str(history),'sha256':hashlib.sha256(original).hexdigest()};receipt.unlink()
  else:raise ValueError('same source ID differs; preserve original')
 result=b.handle(arm,req)
 result['source_service_adapter_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();result['original_helper_request']=raw
 if oldpin:result['preserved_initial_failure']=oldpin
 b.atomic(receipt,result)
 return result
def scan():
 for arm in ['NL_RH','IEANTN_RH']:
  for run in sorted((b.D/'runs').glob('*'+arm+'*')):
   snapshots=sorted(run.glob('checkpoint-*/files'))
   if(run/'submission').exists():snapshots.append(run/'submission')
   for snap in snapshots[-2:]:
    for name in ['SOURCE_REQUESTS.json','source_requests.jsonl']:
     p=snap/name
     if not p.exists():continue
     try:
      requests=b.read(p)['requests']if name.endswith('.json')else[json.loads(line)for line in p.read_text().splitlines()if line.strip()]
      for req in requests:handle(arm,req)
     except Exception as e:b.atomic(b.D/'broker'/arm/'LAST_QUEUE_ERROR_V2.json',{'utc':b.now(),'file':str(p),'error':str(e),'no_mathematical_failure_inferred':True})
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--once',action='store_true');p.add_argument('--self-test',action='store_true');a=p.parse_args()
 if a.self_test:
  for req,key in [({'id':'x','kind':'search','value':'original mathematical paper'},'query'),({'id':'y','kind':'url','value':'https://arxiv.org/abs/2312.05628v4'},'url'),({'id':'z','kind':'fetch','url':'https://arxiv.org/abs/2312.05628v4'},'url')]:
   r=normalized(req)
   if not r.get(key):raise RuntimeError('actual helper schema normalization failed')
  for req in [{'id':'../x','kind':'url','value':'https://arxiv.org/abs/1'},{'id':'a','kind':'bad','value':'x'},{'id':'b','url':'a','query':'b'}]:
   try:normalized(req)
   except ValueError:pass
   else:raise RuntimeError('bad queue request accepted')
  print(json.dumps({'status':'PASS_TYPED_HELPER_AND_LEGACY_SCHEMA_GUARDS','optimization':__import__('sys').flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}));return
 while True:
  scan()
  if a.once:return
  time.sleep(10)
if __name__=='__main__':main()
