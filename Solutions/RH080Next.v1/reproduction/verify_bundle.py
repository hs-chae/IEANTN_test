#!/usr/bin/env python3
"""Offline RH080 bundle part/member verification and optional safe extraction.
This verifies artifact bytes, not mathematical proof or source-first PV.
"""
from __future__ import annotations
import argparse,hashlib,json,os,tarfile,tempfile
from pathlib import Path,PurePosixPath

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def strict_pairs(pairs):
 result={}
 for key,value in pairs:
  need(key not in result,'Duplicate JSON key: '+key);result[key]=value
 return result
def read_json(p):
 return json.loads(p.read_text(),object_pairs_hook=strict_pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('Nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as stream:
  while chunk:=stream.read(8*1024*1024):h.update(chunk)
 return h.hexdigest()
def member_path(name):
 p=PurePosixPath(name)
 need(type(name)is str and name and not p.is_absolute()and '\\'not in name and all(x not in ['', '.', '..']for x in name.split('/')),'Invalid bundle member path')
 return p

def verify_archive(archive,expected_sha=None,extract=None):
 if expected_sha is not None:need(sha(archive)==expected_sha,'Archive SHA256 mismatch')
 with tarfile.open(archive,'r:xz')as tar:
  members=tar.getmembers();names=[m.name for m in members]
  need(len(names)==len(set(names)),'Duplicate archive member')
  need(all(m.isfile()for m in members),'Only regular bundle files are supported')
  for m in members:member_path(m.name)
  need('MANIFEST.json'in names,'Bundle member inventory absent')
  f=tar.extractfile('MANIFEST.json');need(f is not None,'Manifest stream absent')
  manifest_bytes=f.read();manifest=json.loads(manifest_bytes,object_pairs_hook=strict_pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('Nonfinite JSON')))
  need(manifest.get('status')=='EXACT_ARCHIVE_MEMBER_BYTE_INVENTORY_NOT_MATHEMATICAL_ACCEPTANCE','Wrong member manifest kind')
  rows=manifest['files'];need(type(rows)is list,'Member rows absent')
  paths=[r['path']for r in rows];need(len(paths)==len(set(paths)),'Duplicate inventory member')
  need(set(names)==set(paths)|{'MANIFEST.json'},'Archive/member inventory population mismatch')
  for row in rows:
   name=row['path'];member_path(name);need(type(row['bytes'])is int and row['bytes']>=0,'Invalid exact member size')
   m=tar.getmember(name);need(m.size==row['bytes'],'Archive member size mismatch: '+name)
   h=hashlib.sha256();stream=tar.extractfile(m);need(stream is not None,'Member stream absent')
   while chunk:=stream.read(8*1024*1024):h.update(chunk)
   need(h.hexdigest()==row['sha256'],'Archive member SHA256 mismatch: '+name)
  if extract is not None:
   need(not os.path.lexists(extract),'Fresh extraction directory required');extract.mkdir(parents=True)
   for m in members:
    target=extract.joinpath(*member_path(m.name).parts);target.parent.mkdir(parents=True,exist_ok=True)
    stream=tar.extractfile(m);need(stream is not None,'Member stream absent')
    with target.open('xb')as out:
     while chunk:=stream.read(8*1024*1024):out.write(chunk)
    os.chmod(target,0o755 if m.mode&0o111 else 0o644)
   for row in rows:need(sha(extract.joinpath(*member_path(row['path']).parts))==row['sha256'],'Extracted member mismatch')
 return dict(status='PASS_ALL_ARCHIVE_MEMBER_BYTES',files=len(rows),manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),extracted=extract is not None,mathematical_proof_acceptance=False)

def reassemble(parts_file,out):
 j=read_json(parts_file);need(j.get('status')=='EXACT_REPRODUCIBLE_BUNDLE_PART_INVENTORY_NOT_MATHEMATICAL_ACCEPTANCE','Wrong part manifest kind')
 need(not os.path.lexists(out),'Fresh reassembled archive path required')
 rows=j['parts'];need(type(rows)is list and rows,'Nonempty part inventory required')
 names=[r['file']for r in rows];need(len(names)==len(set(names)),'Duplicate part name')
 need(all(type(r['index'])is int for r in rows)and [r['index']for r in rows]==list(range(1,len(rows)+1)),'Part ordering/index mismatch')
 need(type(j['archive_bytes'])is int and j['archive_bytes']>0,'Exact archive size must be an integer')
 for row in rows:
  need(type(row['bytes'])is int and 0<row['bytes']<=8000000,'Invalid part size')
  need(Path(row['file']).name==row['file']and row['file']not in ['.','..'],'Part must be an adjacent filename')
  p=parts_file.parent/row['file'];need(p.is_file()and not p.is_symlink(),'Part absent or not regular')
  need(p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'Part bytes differ: '+row['file'])
 out.parent.mkdir(parents=True,exist_ok=True);temporary=out.with_name(out.name+'.pending');need(not os.path.lexists(temporary),'Fresh temporary archive path required')
 try:
  with temporary.open('xb')as stream:
   for row in rows:
    with(parts_file.parent/row['file']).open('rb')as source:
     while chunk:=source.read(8*1024*1024):stream.write(chunk)
  need(temporary.stat().st_size==j['archive_bytes']and sha(temporary)==j['archive_sha256'],'Reassembled archive differs')
  os.replace(temporary,out)
 except BaseException:
  if temporary.exists():temporary.unlink()
  raise
 return j

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--parts',type=Path);group.add_argument('--archive',type=Path)
 ap.add_argument('--out',type=Path);ap.add_argument('--extract',type=Path);ap.add_argument('--expected-sha256')
 a=ap.parse_args();archive=a.archive;expected=a.expected_sha256
 if a.parts:
  need(a.out is not None,'--parts requires --out');j=reassemble(a.parts,a.out);archive=a.out;expected=j['archive_sha256']
 else:need(a.out is None,'--out is for --parts only')
 result=verify_archive(archive,expected,a.extract);print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
