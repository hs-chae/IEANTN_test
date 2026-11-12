# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
# Extract exact frozen proof sources; no proof is accepted by extraction alone.
import argparse,hashlib,json,zipfile
from pathlib import Path,PurePosixPath
S=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise ValueError(m)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=S/'proof');a=ap.parse_args();out=a.out.resolve();need(not out.exists(),'fresh materialization directory required');need(out!=S and not out.is_relative_to(S/'capsules'),'output outside capsule storage')
 cfg=json.loads((S/'CAPSULES.json').read_text());row=cfg['witness'];archive=S/row['archive'];need(sha(archive)==row['sha256'],'sealed witness ZIP identity')
 prefix='witness/source-only-final-v1/'
 with zipfile.ZipFile(archive)as z:
  need(len(z.namelist())==len(set(z.namelist())),'duplicate archive member');lock=json.loads(z.read(prefix+'SOURCE_LOCK.json'));need(hashlib.sha256(z.read(prefix+'SOURCE_LOCK.json')).hexdigest()==row['source_lock_sha256'],'frozen source lock')
  data=[]
  for f in lock['files']:
   p=PurePosixPath(f['path']);need(not p.is_absolute()and '..'not in p.parts,'unsafe source path');b=z.read(prefix+str(p));need(len(b)==f['bytes']and hashlib.sha256(b).hexdigest()==f['sha256'],'source data identity');data.append((p,b))
 out.mkdir(parents=True)
 for p,b in data:
  dst=out/str(p);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 (out/'SOURCE_LOCK.json').write_text(json.dumps(lock,indent=2)+'\n');(out/'MATERIALIZATION.json').write_text(json.dumps(dict(status='EXACT_SOURCE_EXTRACTION_NO_PROOF_CLAIM',files=len(data),archive_sha256=sha(archive),source_lock_sha256=row['source_lock_sha256']),indent=2)+'\n');print('Extracted',len(data),'exact source inputs')
if __name__=='__main__':main()
