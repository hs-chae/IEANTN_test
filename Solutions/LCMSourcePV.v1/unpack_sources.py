# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
# Recover source/evidence trees from the immutable component archives.
import argparse,hashlib,json,stat,zipfile
from pathlib import Path,PurePosixPath
S=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve();need(not out.exists()and out!=S and not out.is_relative_to(S/'capsules'),'fresh output outside capsule storage');cfg=json.loads((S/'CAPSULES.json').read_text());out.mkdir(parents=True);rows=[];written={}
 for component in ['adaptive','witness','primecover','full_scope']:
  entry=cfg[component];p=S/entry['archive'];need(p.is_file()and p.stat().st_size==entry['bytes']and hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256'],'archive identity '+component)
  with zipfile.ZipFile(p)as z:
   need(len(z.namelist())==len(set(z.namelist())),'duplicate archive member')
   for info in z.infolist():
    if info.is_dir():continue
    name=info.filename
    if component=='adaptive':
     prefix='IEANTN_LCM_ADAPTIVE/';need(name.startswith(prefix),'adaptive prefix');name=name[len(prefix):]
    allowed={'adaptive':('adaptive/',),'witness':('witness/','adaptive/source-only-v1/'),'primecover':('primecover/',),'full_scope':('audit/','resources/')}[component]
    if not name.startswith(allowed):continue
    rel=PurePosixPath(name);need(not rel.is_absolute()and '..'not in rel.parts and not stat.S_ISLNK(info.external_attr>>16),'unsafe member');b=z.read(info);h=hashlib.sha256(b).hexdigest()
    if name in written:need(written[name]==h,'different overlapping source bytes');continue
    dst=out/str(rel);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b);written[name]=h
  rows.append(dict(component=component,archive_sha256=entry['sha256']))
 (out/'CAPSULE_EXTRACTION.json').write_text(json.dumps(dict(status='EXACT_SOURCE_EVIDENCE_EXTRACTION_NO_NEW_PROOF_CLAIM',files=len(written),archives=rows),indent=2)+'\n');print('Extracted',len(written),'source/evidence files')
if __name__=='__main__':main()
