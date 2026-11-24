#!/usr/bin/env python3
"""Export regular reproducibility sources/resources without Git or proof caches.
Historical text sources are retained in this broad packet; only frozen manifests
decide proof coverage. This is a source export, never a verification receipt.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil
I=Path(__file__).resolve().parent;R=I.parents[2]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(root):
 manifests=['Solutions/RHLimit.v1/'+q+'/SOURCE_CLOSURE.json'for q in ['pi','spectral','integration']]
 manifests+=['Solutions/RHOcticPush.v1/integration/corrected/capture/SOURCE_CLOSURE.json','Solutions/RHOcticPush.v1/integration/supplement/audit-corrected-capture/SOURCE_CLOSURE.json']
 count=0
 for rel in manifests:
  m=json.loads((root/rel).read_text())
  for q in m['modules']:
   need(sha(root/q['path'])==q['sha256'],'packet frozen proof source drift:'+q['module'])
   if q.get('original_path')is not None:need(sha(root/q['original_path'])==q['sha256'],'packet author proof source drift:'+q['module'])
   count+=1
 return count
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve();need(not out.exists()and not out.is_relative_to(R),'fresh packet outside source checkout required');need(check(R)==619,'complete exact619 proofsource universe');out.mkdir(parents=True);source=out/'source';source.mkdir();rows=[]
 extensions={'.lean','.py','.json','.yaml','.yml','.toml','.c','.cpp','.cu','.h','.hpp','.md','.txt','.csv','.sh','.in','.lock','.pdf'}
 for dp,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in {'.git','.lake','__pycache__','node_modules'}and not(Path(dp)/d).is_symlink()]
  for name in fs:
   p=Path(dp)/name
   if p.is_symlink()or not(p.suffix in extensions or name in {'lean-toolchain','LICENSE'}):continue
   rel=p.relative_to(R);q=source/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);rows.append({'path':str(rel),'sha256':sha(q),'bytes':q.stat().st_size})
 need(check(source)==619,'relocated packet proof source closure mismatch')
 manifest={'status':'SOURCE_ONLY_EXPORT_NOT_PROOF_ACCEPTANCE','source_root':str(source),'file_count':len(rows),'bytes':sum(q['bytes']for q in rows),'exact_proof_modules':619,'excluded':['.git','.lake','allsymlinks','compiled objects/binaries/caches','non-source extensions'],'generic_context':'Exact generic-only pins in Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json; use integration/portable_context.py to bind a clean pinned install. Application and LeanCert caches are never generic.','files':rows};(out/'SOURCE_PACKET.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k]for k in ['file_count','bytes','exact_proof_modules']}))
if __name__=='__main__':main()
