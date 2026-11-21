#!/usr/bin/env python3
"""Restore an exact source tree from a content-addressed evidence ZIP.

No acceptance assertion can disappear under Python -O/-OO. Receipts live
outside the restored tree, so checking its exact membership stays possible.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,math,os,tempfile,zipfile
def need(b,s):
 if not b:raise ValueError(s)
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def strict(raw):
 def number(s):
  v=float(s);need(math.isfinite(v),'nonfinite number');return v
 return json.loads(raw,object_pairs_hook=pairs,parse_float=number,parse_constant=lambda s:(_ for _ in()).throw(ValueError('nonfinite number')))
def digest(b):return hashlib.sha256(b).hexdigest()
def relative(name):
 need(isinstance(name,str)and name and'\\'not in name,'source path type')
 p=PurePosixPath(name);need(not p.is_absolute()and'..'not in p.parts and str(p)==name,'unsafe/noncanonical path');return p
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('archive',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh restore destination required')
 with zipfile.ZipFile(a.archive)as z:
  names=z.namelist();need(len(names)==len(set(names)),'duplicate archive names');need('MANIFEST.json'in names and'RESTORE.py'in names,'bundle roots')
  manifest_raw=z.read('MANIFEST.json');manifest=strict(manifest_raw);need(manifest.get('schema')=='RH_CONTENT_ADDRESSED_EVIDENCE_V1','manifest schema');rows=manifest['files'];need(isinstance(rows,list)and rows,'nonempty exact source rows');seen=set();objects={}
  for row in rows:
   relative(row['path']);need(row['path']not in seen,'duplicate logical path');seen.add(row['path']);need(type(row['bytes'])is int and row['bytes']>=0,'byte count type');h=row['sha256'];need(isinstance(h,str)and len(h)==64 and all(c in'0123456789abcdef'for c in h),'hash form')
   if h in objects:need(objects[h]==row['bytes'],'same object has conflicting byte counts')
   objects[h]=row['bytes']
  need(set(names)=={'MANIFEST.json','RESTORE.py','README.txt'}|{'objects/'+h for h in objects},'exact physical archive membership')
  need(digest(z.read('RESTORE.py'))==manifest['restore_sha256'],'restorer source identity')
  need(digest(Path(__file__).read_bytes())==manifest['restore_sha256'],'executed restorer identity')
  payloads={}
  for h,size in objects.items():
   raw=z.read('objects/'+h);need(len(raw)==size and digest(raw)==h,'artifact bytes/hash');payloads[h]=raw
  # All archive bytes and logical paths pass before creating an output tree.
  out.mkdir(parents=True)
  for row in rows:
   target=out/row['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(payloads[row['sha256']])
  actual={x.relative_to(out).as_posix()for x in out.rglob('*')if x.is_file()};need(actual==seen,'restored exact membership')
  for row in rows:need(digest((out/row['path']).read_bytes())==row['sha256'],'restored bytes')
 receipt={'status':'PASS_EXACT_EVIDENCE_TREE_RESTORED','archive_sha256':digest(a.archive.read_bytes()),'manifest_sha256':digest(manifest_raw),'logical_file_count':len(rows),'unique_content_objects':len(objects),'logical_bytes':sum(r['bytes']for r in rows),'python_optimization':__import__('sys').flags.optimize,'restorer_sha256':digest(Path(__file__).read_bytes())}
 target=out.parent/(out.name+'-RESTORE_RECEIPT.json');need(not target.exists(),'fresh receipt required');fd,name=tempfile.mkstemp(dir=target.parent,prefix='.'+target.name);temporary=Path(name)
 try:
  with os.fdopen(fd,'w')as f:f.write(json.dumps(receipt,indent=2,allow_nan=False)+'\n')
  os.link(temporary,target)
 finally:temporary.unlink()
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
