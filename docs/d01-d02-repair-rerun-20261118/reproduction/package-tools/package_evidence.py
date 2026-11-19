"""Deterministic public evidence package. Requires exact final Root approval.

Uses the existing archive_portable_source_tree_v2.py tar/gzip conventions;
does not alter or regenerate any scientific source/archive/output.
"""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,io,json,tarfile
A=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('public_inventory',A/'prepare_inventory.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024**2),b''):h.update(b)
 return h.hexdigest()
def validate(ip,approval=None):
 x=m.load(ip);m.need(x['schema']=='PUBLIC_EVIDENCE_SOURCE_INVENTORY_DRAFT_V1','exact inventory schema');names=set();packed_names=set();restored_names=set();decompressed_names=set()
 for z in x['assets']:
  name=m.safe_name(z['archive_path']);m.need(name not in names,'distinct public names');names.add(name)
  m.need(type(z['gzip_json']) is bool,'explicit boolean compression flag')
  if z['gzip_json']:m.need(name.endswith('.json'),'exact compressed JSON suffix');decompressed_names.add(name)
  packed=name+('.gz' if z['gzip_json'] else '');m.safe_name(packed);m.need(packed not in packed_names,'distinct compressed member destinations');packed_names.add(packed);restored_names.add(name)
  p=Path(z['source_path']);m.need(p.is_file() and not p.is_symlink() and p.stat().st_size==z['size'] and digest(p)==z['sha256'],'every exact selected byte remains unchanged')
  m.need(z['privacy']==m.inspect_bytes(p.name,p.read_bytes()),'actual schema/nested-member privacy readback unchanged')
 m.need(not (packed_names & decompressed_names),'compressed and restored destinations remain distinct')
 all_names=packed_names|restored_names
 for name in all_names:
  m.need(not any(str(parent) in all_names for parent in Path(name).parents if str(parent)!='.'),'public file/parent destination collision')
 if approval is not None:
  r=m.load(approval);m.need(r.get('reviewed_by')=='/root' and r.get('status')=='ROOT_APPROVED_EXACT_PUBLIC_EVIDENCE_PACKAGE_BUILD','actual Root package authority')
  m.need(r.get('inventory_sha256')==digest(ip),'Root authority pins this exact inventory')
  m.need(not x['pending_required_assets_and_joins'],'all required assets and actual full numerical readbacks closed')
  decisions=r.get('explicit_privacy_adjudications',{})
  for z in x['assets']:
   if z['privacy']['flags']:
    d=decisions.get(z['archive_path'],{});m.need(d.get('sha256')==z['sha256'] and d.get('disposition')=='ROOT_READ_ACTUAL_BYTES_PUBLIC_SOURCE_NO_PRIVATE_CONTENT' and bool(d.get('reason')),'every flagged actual schema/member explicitly Root adjudicated')
 return x
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--inventory',type=Path,required=True);p.add_argument('--Root-approval',type=Path);p.add_argument('--check',action='store_true');p.add_argument('--out',type=Path);p.add_argument('--part-bytes',type=int,default=6700000);a=p.parse_args()
 x=validate(a.inventory,a.Root_approval)
 if a.check:
  print(json.dumps({'status':'EXACT_INVENTORY_SOURCE_AND_NESTED_SCHEMA_READBACK_ONLY' if a.Root_approval is None else 'PASS_EXACT_ROOT_APPROVED_PACKAGE_METADATA','assets':len(x['assets']),'pending':len(x['pending_required_assets_and_joins']),'flagged':len(x['privacy_flagged_assets']),'archive_created':False},sort_keys=True));return
 m.need(a.Root_approval is not None and a.out is not None,'build needs exact Root approval and fresh output');m.need(1<=a.part_bytes<=6700000,'bounded attachment parts');out=a.out.resolve();m.need(not out.exists(),'fresh package directory');out.mkdir();archive=out/'evidence.tar.gz';members=[]
 # Same regular-only, sorted-name, fixed uid/gid/mtime, empty-name gzip as the existing source archiver.
 entries=[]
 for z in x['assets']:
  b=Path(z['source_path']).read_bytes();name=z['archive_path']
  if z['gzip_json']:
   stream=io.BytesIO()
   with gzip.GzipFile(filename='',fileobj=stream,mode='wb',mtime=0) as g:g.write(b)
   b=stream.getvalue();name+='.gz'
  entries.append((name,b,z))
 m.need(len({z[0] for z in entries})==len(entries),'compressed asset destination collisions rejected')
 with archive.open('xb') as raw,gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as g,tarfile.open(fileobj=g,mode='w|') as t:
  for name,b,z in sorted(entries):
   f=tarfile.TarInfo(name);f.size=len(b);f.uid=f.gid=f.mtime=0;f.uname=f.gname='';f.mode=0o644;t.addfile(f,io.BytesIO(b));members.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'category':z['category'],'original_sha256':z['sha256'],'original_bytes':z['size'],'gzip_JSON':z['gzip_json']})
 parts=[]
 with archive.open('rb') as f:
  i=0
  while True:
   b=f.read(a.part_bytes)
   if not b:break
   i+=1;q=out/('evidence.part%03d'%i)
   with q.open('xb') as g:g.write(b)
   parts.append({'path':q.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 manifest={'schema':'PUBLIC_EVIDENCE_DETERMINISTIC_PART_MANIFEST_V1','archive':{'path':archive.name,'bytes':archive.stat().st_size,'sha256':digest(archive)},'parts':parts,'members':members,'source_inventory_sha256':digest(a.inventory),'Root_approval_sha256':digest(a.Root_approval),'packager_source_sha256':digest(Path(__file__)),'tar_uid_gid_mtime':0,'regular_files_only':True,'gzip_mtime':0,'gzip_filename':'','new_scientific_model_scope_compiler_numerical_runs':0}
 with (out/'PUBLIC_MANIFEST.json').open('x') as f:json.dump(manifest,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'status':'EXACT_ROOT_APPROVED_PUBLIC_ARCHIVE_BUILT_NOT_UPLOADED','archive_sha256':manifest['archive']['sha256'],'parts':len(parts),'members':len(members)},sort_keys=True))
if __name__=='__main__':main()
