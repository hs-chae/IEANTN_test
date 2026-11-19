"""Offline Python3-only part reconstruction and safe, hash-checked extraction."""
from pathlib import Path,PurePosixPath
import argparse,gzip,hashlib,io,json,math,tarfile
def need(v,m):
 if not v:raise ValueError(m)
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024**2),b''):h.update(b)
 return h.hexdigest()
def safe(s):
 need(isinstance(s,str) and '\\' not in s and '\x00' not in s,'canonical POSIX member text');p=PurePosixPath(s);need(not p.is_absolute() and '..' not in p.parts and s not in ('','.') and str(p)==s,'safe canonical relative regular member');return p
def pairs(xs):
 out={}
 for k,v in xs:need(k not in out,'duplicate JSON key');out[k]=v
 return out
def finite(s):
 v=float(s);need(math.isfinite(v),'nonfinite or overflow JSON float');return v
def reject_constant(s):raise ValueError('nonfinite JSON constant '+s)
def load(p):return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=reject_constant)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--parts',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--extract',type=Path);a=p.parse_args();m=load(a.manifest);need(m['schema']=='PUBLIC_EVIDENCE_DETERMINISTIC_PART_MANIFEST_V1','exact manifest schema');need(not a.out.exists(),'fresh reconstructed archive');seen=set()
 for z in m['parts']:
  safe(z['path']);need(z['path'] not in seen,'unique part names');seen.add(z['path']);q=a.parts/z['path'];need(q.is_file() and not q.is_symlink() and q.stat().st_size==z['bytes'] and digest(q)==z['sha256'],'every attachment part byte')
 with a.out.open('xb') as f:
  for z in m['parts']:
   with (a.parts/z['path']).open('rb') as q:
    for b in iter(lambda:q.read(1024**2),b''):f.write(b)
 need(a.out.stat().st_size==m['archive']['bytes'] and digest(a.out)==m['archive']['sha256'],'whole reconstructed archive SHA')
 expected={z['path']:z for z in m['members']};need(len(expected)==len(m['members']),'unique member manifest');seen=set();output_names=set(expected)
 for name,z in expected.items():
  safe(name)
  if z['gzip_JSON']:
   need(name.endswith('.json.gz'),'compressed JSON exact suffix');original=name[:-3];safe(original);need(original not in output_names,'decompressed original destination collision');output_names.add(original)
 for name in output_names:
  need(not any(str(q) in output_names for q in PurePosixPath(name).parents if str(q)!='.'),'file/parent output collision')
 if a.extract is not None:need(not a.extract.exists(),'fresh extraction directory');a.extract.mkdir(parents=True)
 with tarfile.open(a.out,'r:gz') as t:
  for f in t:
   path=safe(f.name);need(f.isfile() and f.name in expected and f.name not in seen,'exact regular-only member set');seen.add(f.name);z=expected[f.name];need(f.size==z['bytes'],'member length');b=t.extractfile(f).read();need(hashlib.sha256(b).hexdigest()==z['sha256'],'member SHA')
   if z['gzip_JSON']:
    with gzip.GzipFile(fileobj=io.BytesIO(b),mode='rb') as g:source=g.read(z['original_bytes']+1)
    need(len(source)==z['original_bytes'] and hashlib.sha256(source).hexdigest()==z['original_sha256'],'exact original JSON restored by bounded decompression')
   else:need(len(b)==z['original_bytes'] and z['sha256']==z['original_sha256'],'scientific source bytes unchanged')
   if a.extract is not None:
    q=a.extract/Path(*path.parts);q.parent.mkdir(parents=True,exist_ok=True)
    with q.open('xb') as g:g.write(b)
    if z['gzip_JSON']:
     original=a.extract/Path(*safe(f.name[:-3]).parts)
     with original.open('xb') as g:g.write(source)
 need(seen==set(expected),'every required member present, none omitted');print(json.dumps({'status':'PASS_ALL_PARTS_ARCHIVE_AND_ORIGINAL_SOURCE_IDENTITIES','members':len(seen),'archive_sha256':m['archive']['sha256'],'extracted':a.extract is not None,'models_compilers_numerics':0},sort_keys=True))
if __name__=='__main__':main()
