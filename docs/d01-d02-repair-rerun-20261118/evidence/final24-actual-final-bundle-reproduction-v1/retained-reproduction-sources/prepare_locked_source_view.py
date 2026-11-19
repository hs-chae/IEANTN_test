"""Separate verified transport gzip copies from exact LOCK source directories.
Original JSON, LOCK files, mathematical sources and algorithms are unchanged.
Default mode plans only; --apply-from requires the exact checked plan.
"""
from pathlib import Path
import argparse,hashlib,json,math,os,tempfile
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def pin(p):return{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def load(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(s):
  v=float(s);need(math.isfinite(v),'nonfinite JSON float');return v
 return json.loads(p.read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda s:(_ for _ in()).throw(ValueError(s)))
def fresh(p,value):
 need(not p.exists(),'fresh receipt');fd,t=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent)
 try:
  with os.fdopen(fd,'w')as f:f.write(json.dumps(value,indent=2)+'\n');f.flush();os.fsync(f.fileno())
  os.link(t,p)
 finally:os.unlink(t)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--bundle-root',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--transport-root',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--apply-from',type=Path);a=p.parse_args();b=a.bundle_root.resolve();t=a.transport_root.absolute();need(b.is_dir()and b!=t and t.parent==b.parent and not t.exists(),'fresh transport sibling outside source bundle');m=load(a.manifest);need(sha(a.manifest)=='665f6b37153f2fc145c50b0008d300cbb450b09d04aabf20b09ac461880e2608','exact already delivered V1 manifest');mpath=b/'PUBLIC_SOURCE_MAP.json';mp=load(mpath)['files'];destinations={v['public_path']for v in mp.values()};declared={v['path']:v for v in m['members']if v['gzip_JSON']};selection=b/'frontiers/FROZEN_FINALIZATION_SELECTION.json';locks={}
 def mapped(ref):
  need(ref['path']in mp,'every source reference explicitly mapped');v=mp[ref['path']];q=b/v['public_path'];need(q.is_file()and not q.is_symlink()and sha(q)==v['sha256']==ref['sha256'],'exact source reference bytes');return q
 for ref in load(selection)['finalizations']:
  f=load(mapped(ref))
  for key in [next(k for k,v in f.items()if k.startswith('complete')and'source'in k and isinstance(v,dict)and'path'in v),next(k for k,v in f.items()if'independent_M_review'in k and isinstance(v,dict)and'path'in v)]:
   q=mapped(f[key]);locks[str(q)]=q
 need(len(locks)==48,'exact24source and24review LOCK directories');moves={};checked=[]
 for lock in sorted(locks.values()):
  j=load(lock);rows=j['files'];need(len(rows)==len({x['path']for x in rows}),'unique original LOCK payload names');root=lock.parent;expected={x['path']for x in rows}|{'LOCK.json'};physical={str(q.relative_to(root))for q in root.rglob('*')if q.is_file()};need(expected<=physical,'no missing original payload can be repaired by transport separation')
  for row in rows:need(sha(root/row['path'])==row['sha256'],'every original locked payload byte preserved')
  extras=physical-expected
  for relative in sorted(extras):
   q=root/relative;name=q.relative_to(b).as_posix();need(name in declared and name not in destinations,'only declared transport extras, never a source-map destination');z=declared[name];need(q.resolve()==q and not q.is_symlink()and q.stat().st_size==z['bytes']and sha(q)==z['sha256'],'exact compressed transport bytes');raw=b/name[:-3];need(raw.is_file()and not raw.is_symlink()and raw.stat().st_size==z['original_bytes']and sha(raw)==z['original_sha256'],'exact restored original JSON bytes before any move');moves[name]={'archive_member':name,'compressed_sha256':z['sha256'],'compressed_bytes':z['bytes'],'restored_original':name[:-3],'original_sha256':z['original_sha256'],'original_bytes':z['original_bytes'],'LOCK_directory':str(root.relative_to(b))}
  checked.append({'LOCK':pin(lock),'expected_names':sorted(expected),'transport_extra_names':sorted(extras)})
 moves=[moves[k]for k in sorted(moves)];plan={'status':'PLAN_ONLY_EXACT_TRANSPORT_GZIP_EXTRAS_NO_SOURCE_CHANGES','helper':pin(Path(__file__).resolve()),'manifest':pin(a.manifest),'source_map':pin(mpath),'selection':pin(selection),'bundle_root':str(b),'transport_root':str(t),'LOCK_directories':checked,'moves':moves,'move_count':len(moves),'compressed_transport_bytes':sum(x['compressed_bytes']for x in moves),'original_payload_or_LOCK_changes':0}
 if a.apply_from is None:fresh(a.receipt,plan);print(json.dumps({'plan':pin(a.receipt),'LOCK_directories':48,'moves':len(moves),'compressed_bytes':plan['compressed_transport_bytes']}));return
 previous=load(a.apply_from);need(previous==plan,'all checked plan/source/map/LOCK identities and exact move set unchanged');t.mkdir();done=[]
 for row in moves:
  q=b/row['archive_member'];target=t/row['archive_member'];target.parent.mkdir(parents=True,exist_ok=True);q.rename(target);need(sha(target)==row['compressed_sha256'],'moved bytes identical');done.append(row)
 for row in checked:
  root=Path(row['LOCK']['path']).parent;need({str(q.relative_to(root))for q in root.rglob('*')if q.is_file()}==set(row['expected_names']),'exact original physical LOCK membership restored')
 fresh(a.receipt,{'status':'PASS_EXACT_TRANSPORT_COPIES_MOVED_ALL48_LOCK_PHYSICAL_MEMBERSHIPS_RESTORED_ORIGINAL_SOURCE_BYTES_UNCHANGED','plan':pin(a.apply_from),'helper':pin(Path(__file__).resolve()),'moves':done,'transport_root':str(t),'all48_original_LOCK_memberships_exact':True,'original_payload_LOCK_algorithms_assumptions_and_primary_archive_changed':False,'deletions':0});print(json.dumps({'receipt':pin(a.receipt),'moved_transport_files':len(done),'original_source_changes':0,'deletions':0}))
if __name__=='__main__':main()
