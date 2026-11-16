#!/usr/bin/env python3
"""Canonicalize ONLY eleven pinned non-proof Lake trace records in a fresh owned bootstrap."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,gzip,hashlib,json,math,os,stat,tempfile
E=Path(__file__).resolve().parents[2]
PIN_SHA='7963460ac2729aa17bbd998daea6dff2ee59bb02141ab0a823924c3b3543cf56'
REF_SHA='5302a02f2d5c9f81cf18a12f3ae17eae46cd622230794cca4c6c38e2f424c1af'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def loads(raw):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(s):
  x=float(s);need(math.isfinite(x),'nonfinite JSON');return x
 return json.loads(raw,object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda s:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def load(p):return loads(Path(p).read_bytes())
def publish(p,d):
 need(not os.path.lexists(p),'fresh publication required');fd,n=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent);tmp=Path(n)
 try:
  with os.fdopen(fd,'w')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(tmp,p)
 finally:tmp.unlink()
def main():
 a=argparse.ArgumentParser();a.add_argument('--environment',type=Path,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--apply',action='store_true');o=a.parse_args();need(not os.path.lexists(o.out),'fresh owned output required');need(o.out.resolve()==o.out.absolute(),'canonical output required');o.out.mkdir(parents=True)
 script=sha(__file__);p=E/'environment/ENVIRONMENT_CONTENTS_RC2_V2.json';ref=E/'environment-bootstrap/reference/APPROVED_PATH_DEPENDENT_TRACES.json.gz';need(sha(p)==PIN_SHA and sha(ref)==REF_SHA,'approved metadata source drift');pin=load(p);approved=loads(gzip.decompress(ref.read_bytes()));need(approved['pinned_manifest_sha256']==PIN_SHA,'metadata reference authority differs');refs={r['path']:r for r in approved['records']};need(len(refs)==11 and all(k.startswith('/evaldeps/mathlib/Cache/')and k.endswith('.trace')for k in refs),'exact eleven trace paths required')
 env=load(o.environment);work=Path(env['work']);need(work.resolve()==work and work.parent==E/'work' and work.name.startswith('environment-'),'fresh experiment-owned environment required');need(o.environment.resolve()==work/'ENVIRONMENT.json','environment receipt must belong to owned work');marker=work/'OWNED_REPRODUCTION_WORK.json';need(marker.is_file()and not marker.is_symlink(),'owned public bootstrap marker required');need(env['status']=='CLEAN_PUBLIC_PINNED_ENVIRONMENT_READY'and env['lean_archive_sha256']==pin['official_archive_sha256']and env['compiler_version']==pin['compiler_version'],'wrong official environment');need(env['bootstrap_script_sha256']==sha(E/'environment-bootstrap/scripts/bootstrap.py'),'fresh approved bootstrap source required')
 roots={'/opt/lean':Path(env['toolchain'])};roots.update({x['target']:Path(x['objects'])for x in env['generic_dependencies']});need(env['generic_dependencies']and pin['generic_pins']==[dict(name=x['name'],commit=x['commit'])for x in env['generic_dependencies']],'generic commit identities differ')
 for root in roots.values():need(root.resolve()==root and root.is_relative_to(work),'generic root escapes fresh owned bootstrap')
 def physical(virtual):
  options=[k for k in roots if virtual==k or virtual.startswith(k+'/')];need(len(options)==1,'unknown generic pin path');return roots[options[0]]/Path(virtual).relative_to(options[0])
 expected={r['path']:r for r in pin['files']};need(len(expected)==pin['file_count']==133055,'complete fixed133055-file manifest required')
 actual=set()
 for virtual,root in roots.items():
  for q in root.rglob('*'):
   if q.is_file():actual.add(str(Path(virtual)/q.relative_to(root)))
 need(actual==set(expected),'generic file membership differs')
 def verify(row,allow_fresh_trace):
  q=physical(row['path']);s=q.stat();h=sha(q);t=q.stat();need((s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)==(t.st_dev,t.st_ino,t.st_size,t.st_mtime_ns),'generic changed while hashing');need((os.readlink(q)if q.is_symlink()else None)==row['symlink_target'],'generic symlink drift')
  if row['path']in refs:
   need(q.resolve()==q and stat.S_ISREG(s.st_mode)and s.st_nlink==1,'trace target must be owned regular nonshared file');r=refs[row['path']];raw=r['utf8'].encode();need(r['sha256']==row['sha256']and r['bytes']==row['bytes']and hashlib.sha256(raw).hexdigest()==row['sha256']and len(raw)==row['bytes'],'canonical trace bytes differ from unchanged pin')
   if not allow_fresh_trace:need(h==row['sha256']and s.st_size==row['bytes'],'postcanonical trace differs')
  else:need(h==row['sha256']and s.st_size==row['bytes'],'nontrace proof/runtime payload drift')
  return dict(path=row['path'],sha256=h,bytes=s.st_size,device=s.st_dev,inode=s.st_ino,mtime_ns=s.st_mtime_ns)
 with ThreadPoolExecutor(max_workers=4)as pool:before=list(pool.map(lambda r:verify(r,True),pin['files']))
 bypath={r['path']:r for r in before};changes=[]
 for k,r in refs.items():
  q=physical(k);backup=o.out/'original-traces'/Path(k).relative_to('/evaldeps/mathlib');backup.parent.mkdir(parents=True,exist_ok=True);backup.write_bytes(q.read_bytes());need(sha(backup)==bypath[k]['sha256'],'fresh metadata backup mismatch');changes.append(dict(path=k,target=str(q),before=bypath[k],approved_sha256=r['sha256'],backup=str(backup.relative_to(o.out))))
 publish(o.out/'PREPARED.json',dict(status='COMPLETE_RUNTIME_EXACT_EXCEPT_ELEVEN_APPROVED_METADATA_PATHS',apply_requested=o.apply,source_sha256=script,pin_sha256=PIN_SHA,reference_sha256=REF_SHA,environment_sha256=sha(o.environment),files_checked=len(before),nontrace_payloads_exact=len(before)-11,changes=changes))
 if o.apply:
  for r in changes:
   q=Path(r['target']);s=q.stat();need(q.resolve()==q and (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)==tuple(r['before'][k]for k in ['device','inode','bytes','mtime_ns'])and sha(q)==r['before']['sha256'],'trace changed after approval');fd,n=tempfile.mkstemp(prefix='.'+q.name+'.',dir=q.parent);tmp=Path(n)
   try:
    with os.fdopen(fd,'wb')as f:f.write(refs[r['path']]['utf8'].encode());f.flush();os.fsync(f.fileno())
    os.replace(tmp,q)
   finally:
    if tmp.exists():tmp.unlink()
  with ThreadPoolExecutor(max_workers=4)as pool:after=list(pool.map(lambda r:verify(r,False),pin['files']))
  need(sha(__file__)==script and sha(p)==PIN_SHA and sha(ref)==REF_SHA,'normalizer authority changed');publish(o.out/'RECEIPT.json',dict(status='ALL133055_PINNED_BYTES_MATCH_AFTER_EXACT_ELEVEN_METADATA_CANONICALIZATION',source_sha256=script,pin_sha256=PIN_SHA,reference_sha256=REF_SHA,environment_sha256=sha(o.environment),files_checked=len(after),proof_payloads_changed=0,metadata_paths=len(changes),fresh_original_metadata_preserved=True,prepared_sha256=sha(o.out/'PREPARED.json')))
 print('METADATA_CANONICALIZATION_'+('APPLIED'if o.apply else'PREPARED'),len(before),'files checked')
if __name__=='__main__':main()
