#!/usr/bin/env python3
"""Rehash all initially supplied application source/cache files after discovery."""
from pathlib import Path
import concurrent.futures,datetime,hashlib,json,time
import os
R=Path(__file__).resolve().parents[1];O=R/'publication/POST_RUN_INITIAL_INPUT_RECHECK.json'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
started=time.monotonic();results=[]
for name in ['FULL_IEANTN','APPLICATION_CACHE']:
 path=R/'protocol/trees'/(name+'.json');j=json.loads(path.read_text());root=Path(j['root'])
 def check(row):
  p=root/row['path']
  if 'symlink' in row:
   return None if p.is_symlink()and os.readlink(p)==row['symlink'] else {'path':row['path'],'error':'initial symlink changed'}
  if not p.is_file():return {'path':row['path'],'error':'initial file absent'}
  if p.stat().st_size!=row['bytes']or sha(p)!=row['sha256']:return {'path':row['path'],'error':'initial bytes changed'}
  return None
 with concurrent.futures.ThreadPoolExecutor(max_workers=8)as pool:bad=[r for r in pool.map(check,j['files'])if r]
 results.append({'manifest':name,'manifest_sha256':sha(path),'initial_file_count':len(j['files']),'initial_bytes':sum(r.get('bytes',0)for r in j['files']),'differences':bad,'new_postlock_files_are_not_initial_inputs':True})
result={'schema':'RH_POST_RUN_INITIAL_SOURCE_CACHE_REHASH_V1','status':'PASS_ALL_INITIAL_BYTES_UNCHANGED'if not any(r['differences']for r in results)else'INITIAL_INPUT_CHANGE_DETECTED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-started,'rows':results,'script_sha256':sha(__file__)}
O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if result['status']!='PASS_ALL_INITIAL_BYTES_UNCHANGED':raise SystemExit(1)
